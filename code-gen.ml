#use "semantic-analyser.ml";;
open Semantics;;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
  
  (*remove at the end*)
  (*val test_make_consts_tbl : string ->(constant * (int * string)) list
  val test_make_fvars_tbl : string -> (string * int) list
  val test_generate : string -> string*)
end;;


exception X_get_offset_error;;
exception X_Code_gen_error;;


(*-----------------------------CONST TABLE-------------------------------*)


let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

let compare_consts e1 e2 =
  match e1, e2 with
	| Sexpr(x), Sexpr(y) -> sexpr_eq x y
	| Void, Void -> true
	| _ -> false;;

let compare_fvars e1 e2 =
  match e1, e2 with
	| VarFree(x), VarFree(y) ->  x=y
	| _ -> false;;


let rec list_contains x list comparator=
  (match list with
  | [] ->false
  | car :: cdr -> comparator car x || list_contains x cdr comparator);;

let rec list_to_set list set comparator =
  (match list with
   | []-> set
   | car::cdr -> if (list_contains car set comparator) 
                  then (list_to_set cdr set comparator)
                  else list_to_set cdr (set @ [car]) comparator
  );;

let rec make_sub_consts x list_to_return =(
  match x with
  | Sexpr(Symbol(y)) -> [Sexpr(String(y));x] @ list_to_return
	| Sexpr(Pair(car, cdr)) -> 
      let lst = make_sub_consts (Sexpr(cdr)) ([(Sexpr(car));(Sexpr(cdr));x] @ list_to_return) in
      make_sub_consts (Sexpr(car)) lst
  | _ -> [x] @ list_to_return
);;

let expand_const_list list = 
    let mapped = List.map (fun (x) -> make_sub_consts x []) list in
    List.flatten mapped;;
              

let rec consts_of_sexpr expr list_to_return =  
(match expr with
	| Const'(Void) -> list_to_return
  | Const'(Sexpr(sexp)) -> list_to_return @ [Sexpr(sexp)]
  | Var'(x) -> list_to_return
  | Box'(x)-> list_to_return
  | BoxGet'(x) -> list_to_return
  | BoxSet'(x, y) -> list_to_return @ (consts_of_sexpr y [])
  | If' (test, dit, dif) -> list_to_return @ ((consts_of_sexpr test []) @ (consts_of_sexpr dit []) @ (consts_of_sexpr dif []))
  | Seq'(list) -> list_to_return @ (List.flatten (List.map (fun (x) -> consts_of_sexpr x []) list ))
  | Set'(var, value) -> list_to_return @  (consts_of_sexpr value [])
  | Def'(var, value) -> list_to_return @  (consts_of_sexpr value [])
  | Or'(list) -> list_to_return @ (List.flatten (List.map (fun (x) -> consts_of_sexpr x []) list ))
  | LambdaSimple'(params, body) -> list_to_return @ (consts_of_sexpr body [])
  | LambdaOpt'(params, variadic, body) -> list_to_return @ (consts_of_sexpr body [])
  | Applic'(rator, rands) -> list_to_return @ (List.flatten (List.map (fun (x) -> consts_of_sexpr x [] ) ([rator] @ rands)))
  | ApplicTP'(rator, rands) ->  list_to_return @ (List.flatten (List.map (fun (x) -> consts_of_sexpr x [] ) ([rator] @ rands)))
) ;;

let consts_of_sexprs asts =
List.flatten (List.map (fun (x) -> consts_of_sexpr x []) asts);;


let make_tuple a b c =
  [a, (b,c)];;
  
let rec list_t_string list= 
(match list with
| [] -> ""
| [x] -> x
| car::cdr -> car^", " ^list_t_string cdr
);;
   
let make_assci_string s =
  let assci_list = string_to_list s in
  let assci_list = List.map (fun(x)-> string_of_int (int_of_char x)) assci_list in
  list_t_string assci_list;;


let rec get_offset_const_tbl x list = 
(match list with 
| [] -> -1
| (Void, (offset, y))::cdr  -> get_offset_const_tbl x cdr
| (Sexpr(z), (offset, y))::cdr ->
  if(sexpr_eq z x)
  then offset
  else get_offset_const_tbl x cdr
);;

let rec get_offset_fvar_tbl x list = 
(match list with 
| [] -> -1
| (name, offset)::cdr  -> 
  if(name = x)
  then offset
  else get_offset_fvar_tbl x cdr
);;

let rec create_tuples_list offset list list_to_return =
  (match list with
  | []-> list_to_return
  | Void::cdr -> create_tuples_list (offset+1) cdr (list_to_return @ (make_tuple Void offset "db T_VOID"))
  | Sexpr(Nil)::cdr -> create_tuples_list (offset+1) cdr (list_to_return @ (make_tuple (Sexpr(Nil)) offset "db T_NIL"))
  | Sexpr(Bool(false))::cdr -> create_tuples_list (offset+1+1) cdr (list_to_return @ (make_tuple (Sexpr(Bool(false))) offset "db T_BOOL, 0"))
  | Sexpr(Bool(true))::cdr -> create_tuples_list (offset+1+1) cdr (list_to_return @ (make_tuple (Sexpr(Bool(true))) offset "db T_BOOL, 1"))
  | Sexpr(Number(Fraction(x,y)))::cdr -> create_tuples_list (offset+1+8+8) cdr (list_to_return @ (make_tuple (Sexpr(Number(Fraction(x,y)))) offset ("MAKE_LITERAL_RATIONAL("^(string_of_int x)^","^(string_of_int y)^")")))
  | Sexpr(Number(Float(x)))::cdr -> create_tuples_list (offset+1+8) cdr (list_to_return @ (make_tuple (Sexpr(Number(Float(x)))) offset ("MAKE_LITERAL_FLOAT("^(string_of_float x)^")")))
  
  | Sexpr(Char(x))::cdr -> create_tuples_list (offset+1+1) cdr (list_to_return @ (make_tuple (Sexpr(Char(x))) offset ("MAKE_LITERAL_CHAR("^(string_of_int (int_of_char x))^")")))
  | Sexpr(String(x))::cdr ->  let make_string_string = "MAKE_LITERAL_STRING \""^x^"\"" in
                        create_tuples_list (offset+1+8+(String.length x)) cdr (list_to_return @ (make_tuple (Sexpr(String(x))) offset make_string_string))

  | Sexpr(Symbol(x))::cdr ->
      let abs_adress = "const_tbl+"^ (string_of_int (get_offset_const_tbl (String(x)) list_to_return)) in  
      create_tuples_list (offset+1+8) cdr (list_to_return @ (make_tuple (Sexpr(Symbol(x))) offset ("MAKE_LITERAL_SYMBOL("^ abs_adress^")")))
  | Sexpr(Pair(a,b))::cdr -> 
    let car_offset = string_of_int (get_offset_const_tbl a list_to_return) in
    let cdr_offset = string_of_int (get_offset_const_tbl b list_to_return) in 
    let adrss= ("MAKE_LITERAL_PAIR(const_tbl+"^car_offset^", const_tbl+"^cdr_offset^")") in
    create_tuples_list (offset+1+8+8) cdr (list_to_return @ (make_tuple (Sexpr(Pair(a,b))) offset adrss))
  );;


(*-----------------------------FVAR TABLE-------------------------------*)
  let rec fvars_of_sexpr expr list_to_return =  
(match expr with
	| Const'(x) -> list_to_return
  | Var'(VarFree(x)) -> list_to_return @ [VarFree(x)]
  | Var'(x) -> list_to_return
  | Box'(x)-> list_to_return
  | BoxGet'(x) -> list_to_return
  | BoxSet'(x, y) -> list_to_return @ (fvars_of_sexpr y [])
  | If' (test, dit, dif) -> list_to_return @ ((fvars_of_sexpr test []) @ (fvars_of_sexpr dit []) @ (fvars_of_sexpr dif []))
  | Seq'(list) -> list_to_return @ (List.flatten (List.map (fun (x) -> fvars_of_sexpr x []) list ))
  | Set'(x, y) -> list_to_return @ (fvars_of_sexpr (Var'(x)) []) @ (fvars_of_sexpr y [])
  | Def'(x, y) -> list_to_return @ (fvars_of_sexpr (Var'(x)) []) @ (fvars_of_sexpr y [])
  | Or'(list) -> list_to_return @ (List.flatten (List.map (fun (x) -> fvars_of_sexpr x []) list ))
  | LambdaSimple'(params, body) -> list_to_return @ (fvars_of_sexpr body [])
  | LambdaOpt'(params, variadic, body) -> list_to_return @ (fvars_of_sexpr body [])
  | Applic'(rator, rands) -> list_to_return @ (List.flatten (List.map (fun (x) -> fvars_of_sexpr x [] ) ([rator] @ rands)))
  | ApplicTP'(rator, rands) ->  list_to_return @ (List.flatten (List.map (fun (x) -> fvars_of_sexpr x [] ) ([rator] @ rands)))
) ;;

let fvars_of_sexprs asts =
List.flatten (List.map (fun (x) -> fvars_of_sexpr x []) asts);;

let rec create_pairs_list offset list =
  (match list with
  | VarFree(x) :: cdr -> [(x,offset)] @ (create_pairs_list (offset+1) cdr)
  | _-> []
  );;

(*********************************GENERATE***********************************************)

let label_counter = ref 0;;

let const_string c consts = ";Const
                            mov rax, const_tbl+"^(string_of_int(get_offset_const_tbl c consts))^"\n";;
                              
let var_param_string minor= ";VarParam
                            mov rax, qword[rbp+8*(4+"^(string_of_int minor)^")]\n";;

let set_param_string minor = ";Set(VarParam)
                              mov qword[rbp+8*(4+"^(string_of_int minor)^")], rax
                              mov rax, SOB_VOID_ADDRESS\n";;
                    
let var_bound_string major minor = ";VarBound
                                    mov rax, qword[rbp+8*2]
                                    mov rax, qword[rax+8*"^(string_of_int major)^"]
                                    mov rax, qword[rax+8*"^(string_of_int minor)^"]\n";;

let set_bound_string major minor = ";Set(VarBound)
                                   mov rbx, qword[rbp+8*2]
                                   mov rbx, qword[rbx+8*"^(string_of_int major)^"]
                                   mov qword[rbx+8*"^(string_of_int minor)^"], rax
                                   mov rax, SOB_VOID_ADDRESS\n";;
                        
let var_free_string v fvars  = ";VarFree
                               mov rax, qword[fvar_tbl+8*"^(string_of_int (get_offset_fvar_tbl v fvars))^"]\n";;

let set_free_string v fvars = ";Set(VarFree)
                                mov qword[fvar_tbl+8*"^(string_of_int (get_offset_fvar_tbl v fvars))^"], rax
                                mov rax, SOB_VOID_ADDRESS\n";;

let or_string index = ";Or
                      cmp rax, SOB_FALSE_ADDRESS
                      jne Lexit"^(string_of_int index)^"\n" ;;

let box_get_string = ";BoxGet
                      mov rax, qword [rax]\n";;

let box_set_string = ";BoxSet
                      pop qword[rax]
                      mov rax, SOB_VOID_ADDRESS\n";;


(********************GENERATE - LAMBDA HELP FUNCTIONS************************************)

(*@PRE r8 is pointer to extended env
  r9 is a temp var to  env[i]*)
let rec copy_env_vectors_string i env_size =
if(i==(env_size-1)) 
then ""
else "mov qword r9, [rbx + "^ (string_of_int (i*8)) ^ "] ;r9 = env["^(string_of_int i)^"]
 		 mov qword [r8 + "^ (string_of_int ((i+1)*8)) ^"], r9\n"^  
     (copy_env_vectors_string (i+1) env_size);;


(*@pre - none
  @post rcx is the new vector we should add to extend_env[0] *)
let copy_stack_params_string index =
  ";Copy the parameter from the stack to new vector
  mov r10, qword [rbp+8*3] ;r10=number of args
  shl r10,3
  MALLOC rcx, r10 ;allocate new space for the stack args
  mov r10, qword [rbp+3*8] ; r10 = number of args
	mov r11, 0 ; r11 = loop counter
	copy_stack_args"^(string_of_int index)^":
  cmp r10, 0
  je copy_stack_args_end"^(string_of_int index)^"\n"^
  "add r11,4
  mov rbx, [rbp + 8*r11] ;rbx = args[i]
  sub r11,4
  mov [rcx + 8*r11], rbx ;extEnv[0][i] =args[i]
  dec r10
  inc r11
  jmp copy_stack_args"^(string_of_int index)^"\n"^
  "copy_stack_args_end"^(string_of_int index)^":\n";;

(* r8 = new env pointer
   rbx = old env pointer
   rcx = pointer to new args vector *)
let lambda_pre_string depth index= 
  let env_size_in_bytes= string_of_int ((depth+1)*8) in
  let env_size = (depth+1) in
  "; Start prepare the new lambda environment
  MALLOC r8, "^env_size_in_bytes ^ " ;r8 = extend_env pointer
  mov qword rbx, [rbp + 8*2] ;rbx = env pointer\n"^
  (copy_env_vectors_string 0 env_size) ^ "\n" ^ 
  (copy_stack_params_string index) ^ "\n"^
  "mov qword [r8], rcx \n";;


let extend_env args index depth =
let env = 
    if(depth==0) 
    then "SOB_NIL_ADDRESS"
    else "r8" in
let pre = if(depth==0) 
          then "" 
          else lambda_pre_string depth index in
pre^"MAKE_CLOSURE(rax,"^env^",Lcode"^(string_of_int index)^")\n"^"jmp Lcont"^(string_of_int index)^"\n";;


(*FOR LAMBDA OPT
1. check if need to shrink or enlarge the stack 
      (counter = subtract num of args in stack - num of fixes params)
2. if enlarge -> shift stack down by 1 and push Nil
3. if shrink then ->
              a. create the list  
              b. shift the stack up by (counter -1)
              c. put the list from step 1 in the buttom of the frame*)

(*UNDO THE PUSH RBP and MOV RBP, RSP*)
(*WE STOPPED HERE*)
let adjust_stack i args =
    let index = string_of_int i in
    let fixed_args_size = string_of_int (List.length args) in

    ";check for shrink/enlarge
    push rbp
    mov rbp,rsp
    mov r8, [rbp+ 8*3]  ;r8=actual args count
    sub r8, "^fixed_args_size^"; r8= |actual_param_count - fixed_args_count|
    cmp r8,0
    je enlarge_stack"^index^"\n"^    
  
    ";shrink_stack
    mov r13, r8                      ;store the num of vars in option
    mov r9, qword [rbp+ (3*8)]        ;r9=total args count
    mov r11, SOB_NIL_ADDRESS
    create_args_list_loop"^index^":
    cmp r8,0                      ;r8=number of args in the list.
    je create_args_list_loop_end"^index^"\n"^
    "add r9,3
    mov r10, qword [rbp + 8*r9]   ;r10= arg(i)
    sub r9,3
    MAKE_PAIR(r12,r10,r11)            ;r12=pair(r10,r11)
    mov r11,r12
    dec r8
    dec r9
    jmp create_args_list_loop"^index^"\n"^

    ";r12 is the list we need to push
     create_args_list_loop_end"^index^":
     mov r9, qword [rbp+ (3*8)]        ;r9=total args count
     mov [rbp + 8*(3+r9)], r12         ;arg[n] = new list                
    
    ;shrink up by r13 - 1, r9 is first param to shift, r13 is by how much to shift, r8 is num of elements to shift
    sub r9, r13
    dec r13
    add r9, 3
    shrink_stack_loop"^index^":
    cmp r9, -1
    je end_shrink_stack_loop"^index^"\n"^
    "mov r10, qword [rbp + 8*r9] ;r10 is tmp
    add r9,r13
    mov [rbp + 8*r9], r10
    sub r9,r13
    dec r9
    jmp shrink_stack_loop"^index^"\n"^
    
    "end_shrink_stack_loop"^index^":
    shl r13,3
    add rbp, r13
    add rsp, r13
    shr r13,3
    jmp end_fix_stack"^index^"\n"^
    

    "enlarge_stack"^index^":  ;enlarge stack by 1 and push nill at the bottom of the stack
    mov r8,4        ;size of [rbp,ret,N,()]
    add r8,"^fixed_args_size^" ;r8=size of the frame
    mov rcx,0       ;rcx = offset

    enlarge_stack_loop"^index^":
      cmp r8,0
      je end_enlarge_stack_loop"^index^"\n"^
      "mov r9, qword [rbp+ 8*rcx]    ;r9=temp var to move down
      mov [rbp+ (8*rcx) -8],r9        ;push the var 1 spot down in the stack
      inc rcx                       ;inc the offset
      dec r8                        ;dec the loop counter
      jmp enlarge_stack_loop"^index^"\n"^

    "end_enlarge_stack_loop"^index^":
      mov r8, SOB_NIL_ADDRESS
      dec rcx
      mov [rbp+ 8*rcx], r8    ;push nill at the bottom of the stack
      sub rbp,8               ;new pos for rbp
      sub rsp,8               ;new pos for rsp
      
      end_fix_stack"^index^":
      mov r8, "^fixed_args_size^"\n"^
      "inc r8
      mov [rbp +8*3], r8
      pop rbp\n"
      





(*********************************GENERATE APPLIC HELP FUNCTIONS***********************************************)
let is_closure_string index = 
    "push qword [rax+TYPE_SIZE]         ;push env
	  call [rax+TYPE_SIZE+WORD_SIZE]      ;call closure code
    add rsp, 8*1                        ;pop env
    pop rbx                             ;pop arg count
    shl rbx, 3                          ;rbx = rbx * 8
    add rsp, rbx                        ; pop args
    jmp done_applic"^index^"\n";;

    (*@PRE
  r15- rbp of f
  rbp- base pointer to g.
  rsp - base pointer to h
  DO NOT touch the rax!!
  
1. r15<- [rbp] -old rbp of f stack frame
2. replace m+3 elements
3. pop |n-m|+1 elements
4. rbp <- r15
*)
let fix_the_stack_applic_tp_string index = 
    ";FIX THE STACK IN APPLIC TP
    mov r15, [rbp]                      ;store the old f
    mov r8, qword [rbp + 3*8] ;r8=n


    add r8,3
    mov r14, r8                         ;for later usage of m and n
    inc r14
    shl r8,3
    add r8, rbp
    mov r9, r8                          ;r9=pointer to args_g(n)
    mov r8, qword [rsp+2*8]             ;r8=m
    add r8, 2
    shl r8, 3
    add r8, rsp
    mov r10, r8                         ;r10 = pointer to args_h(m)

    mov r8,qword [rsp+2*8]
    add r8,3                            ;r8=m+3
    replace_elements_loop"^index^":
    cmp r8,0
    je replace_elements_loop_end"^index^"\n"^
      "mov r11,qword[r10]
      mov [r9],r11
      sub r10,8
      sub r9,8
      dec r8
      jmp replace_elements_loop"^index^"\n"^

    ";r9=the new location the rsp should point to.
    replace_elements_loop_end"^index^":
    shl r14,3
    add rsp,r14
    mov rbp, r15\n";;

let is_closure_string_tp index =
    "push qword [rax+TYPE_SIZE] ;push env
     push qword [rbp + 8 * 1]\n"^
    (fix_the_stack_applic_tp_string index)^
    "jmp [rax+TYPE_SIZE+WORD_SIZE] ;jump to closure code\n";;


let is_not_closure_string index = 
	      "not_closure"^index^":
        mov rdi, 1
        mov rax, 60 ; system call 60 is exit
        syscall\n";;
	    

(********************GENERATE - END OF LAMBDA HELP FUNCTIONS************************************)
                                
let rec generate_code consts fvars e depth =
(match e with
| Const'(Sexpr(c)) -> const_string c consts
| Const'(Void) -> ";Const 
                  mov rax, const_tbl\n"
| Var'(VarParam(_, minor)) -> var_param_string minor
| Set'(VarParam(_, minor),value) -> (generate_code consts fvars value depth) ^ "\n" ^ (set_param_string minor) 
| Var'(VarBound(_, major, minor)) -> var_bound_string major minor
| Set'((VarBound(_,major,minor)),value) -> (generate_code consts fvars value depth) ^ "\n" ^ (set_bound_string major minor)
| Var'(VarFree(v)) -> var_free_string v fvars
| Set'(VarFree(v),value) -> (generate_code consts fvars value depth) ^ "\n" ^ (set_free_string v fvars)
| Def'(VarFree(x), value) -> ";Define\n" ^ (generate_code consts fvars value depth) ^ "\n"^
	    							   "mov qword [fvar_tbl+8*"^(string_of_int (get_offset_fvar_tbl x fvars)) ^ "], rax
	    							   mov rax, SOB_VOID_ADDRESS\n"
| Seq'(list) -> ";Seq\n" ^ List.fold_left (^) "" (List.map (fun (x)-> generate_code consts fvars x depth) list)
| Or'(list) ->let index = !label_counter in
              (label_counter := index+1);
              let rev_list = List.rev list in
              let last = List.hd rev_list in
              let without_last = List.tl rev_list in
              let without_last = List.rev without_last in
             ";Or\n" ^  (List.fold_left (^) "" (List.map (fun (x)-> (generate_code consts fvars x depth) ^ (or_string index)) without_last)) ^
              (generate_code consts fvars last depth) ^"Lexit"^(string_of_int index)^":\n"
| If' (test, dit, dif) -> let index = !label_counter in
                          (label_counter := index+1);
                          let strindex = string_of_int index in
                          (generate_code consts fvars test depth) ^
                          "cmp rax, SOB_FALSE_ADDRESS
                          je Lelse"^strindex^"\n"^
                          (generate_code consts fvars dit depth) ^
                          "jmp Lexit"^strindex^"\n"^
                          "Lelse"^strindex^":\n"^
                          (generate_code consts fvars dif depth)^
                          "Lexit"^strindex^":\n"
| BoxGet'(v) ->";BoxGet\n"^
                (generate_code consts fvars (Var'(v)) depth)^ box_get_string
| BoxSet'(v,value) ->";BoxSet\n"^
                      (generate_code consts fvars value depth)^
                      "push rax\n"^
                      (generate_code consts fvars (Var'(v)) depth) ^
                      box_set_string    
| Box'(v) -> ";Box(v)\n" ^ 
  (generate_code consts fvars (Var'(v)) depth) ^
  "push rdx
  MALLOC rdx, 8
  mov [rdx], rax
  mov rax, rdx
  pop rdx\n"                                 
| LambdaSimple'(args,body) -> ";LambdaSimple\n" ^ (generate_code_lambda consts fvars args body depth "simple")
| LambdaOpt'(args, vs, body ) ->";LambdaOpt\n" ^ (generate_code_lambda consts fvars args body depth "opt")
| Applic'(rator, rands) ->";Applic\n" ^ (handle_applic consts fvars depth rator rands is_closure_string)
| ApplicTP'(rator, rands) ->";ApplicTP\n"^ (handle_applic consts fvars depth rator rands is_closure_string_tp)               
|_->  (*"THIS IS THE FUCKED UP EXPR" ^(print_expr e)*)
      raise X_Code_gen_error                  
)

and handle_applic consts fvars depth rator rands f = (
   let index = !label_counter in
   (label_counter := index+1);
   let str_index =string_of_int index in
   let prefix = applic_prefix_string consts fvars depth rator rands str_index in
   let is_closure = f str_index in
   let is_not_closure = is_not_closure_string str_index in
   prefix^is_closure^is_not_closure^"done_applic"^str_index^":\n")

and applic_prefix_string consts fvars depth rator rands index =(
  let rev_rands = List.rev rands in
  let body = List.map (fun (x) -> (generate_code consts fvars x depth)^"push rax\n") rev_rands in
  let body = List.fold_left (^) "" body in
  let body = body^"push "^(string_of_int (List.length rands))^"\n" in
  let eval = generate_code consts fvars rator depth in
  let verify_closure= "cmp byte [rax], T_CLOSURE
	    	              jne not_closure"^index^"\n" in
  body^eval^verify_closure)

and generate_code_lambda consts fvars args body depth tag =
  let index = !label_counter in
  (label_counter := index+1);
  let is_opt = if(tag = "simple") then "" else (adjust_stack index args) in
  let first = extend_env args index depth in
  let pre = "Lcode"^(string_of_int index)^":\n"^
             is_opt^"\n"^
             "push rbp
             mov rbp,rsp\n" in
  let body =(generate_code consts fvars body (depth + 1)) in
  let ending = "leave
	              ret 
	              Lcont"^(string_of_int index)^":\n" in
  first^pre^body^ending;;


module Code_Gen : CODE_GEN = struct


  let make_consts_tbl asts = 
  let step1 = consts_of_sexprs asts in (*Sexpr List *)
  let step1 = [Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))]  @ step1 in (*Sexpr List *)
  let step2 = list_to_set step1 [] compare_consts in (*Sexpr List *)
  let step3 = expand_const_list step2 in (*Sexpr List *)
  let step4 = list_to_set step3 [] compare_consts in (*Sexpr List *)
  let step5= create_tuples_list 0 step4 [] in  (*(constant * (int * string)) list*)
  step5;;
  

  let make_fvars_tbl asts = 
  let step1 = fvars_of_sexprs asts in
  let prim_list = [VarFree("boolean?");VarFree("flonum?");VarFree("rational?");VarFree("pair?");
                   VarFree("null?");VarFree("char?");VarFree("string?");
                   VarFree("procedure?");VarFree("symbol?");VarFree("string-length");
                   VarFree("string-ref");VarFree("string-set!");VarFree("make-string");VarFree("symbol->string");
                   VarFree("char->integer");VarFree("integer->char");VarFree("exact->inexact");VarFree("eq?");
                   VarFree("+");VarFree("*");VarFree("/");VarFree("=");VarFree("<");
                   VarFree("numerator");VarFree("denominator");VarFree("gcd");
                   VarFree("car");VarFree("cdr");VarFree("cons");
                   VarFree("set-car!");VarFree("set-cdr!");VarFree("apply")] in
  let step1 = prim_list @ step1 in
  let step2 = list_to_set step1 [] compare_fvars in
  let step3 = create_pairs_list 0 step2 in 
  step3;;


  let generate consts fvars e = generate_code consts fvars e 0;;

(******************************TESTS*********************************************)


  let test_make_consts_tbl value = 
    let sexpr_list= Reader.read_sexprs value in
    let parsed =  Tag_Parser.tag_parse_expressions sexpr_list in
    let f =( fun (x) ->
    match x with
    |[z] -> z
    |_-> raise X_syntax_error) in
    let v = f parsed in
    let v = run_semantics v in
    make_consts_tbl [v];;

    let test_make_fvars_tbl value = 
    let sexpr_list= Reader.read_sexprs value in
    let parsed =  Tag_Parser.tag_parse_expressions sexpr_list in
    let f = fun (x) ->
    match x with
    |[z] -> z
    |_-> raise X_syntax_error in
    let v = f parsed in
    let v = run_semantics v in
    make_fvars_tbl [v];;


  let test_generate value =
    let sexpr_list= Reader.read_sexprs value in
    let parsed =  Tag_Parser.tag_parse_expressions sexpr_list in
    let f = fun (x) ->
    match x with
    |[z] -> z
    |_-> raise X_syntax_error in
    let v = f parsed in
    let v = run_semantics v in
    let consts= make_consts_tbl [v] in 
    let fvars = make_fvars_tbl [v] in
    let s = generate consts fvars v in
    (print_string s);
    "";;

end;;
