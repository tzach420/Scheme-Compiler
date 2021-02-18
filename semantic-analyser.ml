#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

exception X_update_vars_indeces_error;;
exception X_box_lambda_error;;
exception X_box_annotate_error;;
exception X_find_depth_error;;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;	
                      
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct


(*----------------------------ANNOTATE LEXICAL ADRESS----------------------------------*)

let rec get_minor_index list x index =(
  match list with
  |[] -> index
  | first::rest ->( 
    if(String.equal first x)
    then index
    else get_minor_index rest x (index+1)
  ));;

let find_var_type list x index = (
  if (index==(-1))
  then VarParam(x,(get_minor_index list x 0))
  else VarBound (x,index,(get_minor_index list x 0))
);;

let rec make_var' x env index =(
  match env with
  |[] -> VarFree(x)
  | first::rest -> 
    if (List.mem x first) 
    then find_var_type first x index
    else (make_var' x rest (index +1))
);;


let rec handle_annot env e  = (
  match e with
  | Const(x) -> Const'(x)
  | Var(x) -> Var'(make_var' x env (-1))
  | If(test, dit, dif) -> If'(handle_annot env test, handle_annot env dit, handle_annot env dif)
  | Seq(x) -> Seq'(List.map (fun y -> handle_annot env y) x)
  | Set(Var(x),y) -> Set'(make_var' x env (-1), handle_annot env y)
  | Def(Var(x),y) -> Def'(make_var' x env (-1), handle_annot env y)
  | Or(x) -> Or'(List.map (fun y -> handle_annot env y) x)
  | LambdaSimple(args, exprs) -> LambdaSimple'(args, (handle_annot (args::env) exprs))
  | LambdaOpt(params, variadic, body) -> LambdaOpt'(params, variadic, (handle_annot ((params@[variadic])::env) body))
  | Applic(rator, rands) -> Applic'(handle_annot env rator, List.map (fun x -> handle_annot env x) rands)
  | _ -> raise X_syntax_error);;



(*-------------------------------------------------------------------------------*)


(*----------------------------ANNOTATE TAIL CALLS----------------------------------*)


let get_last_arg list = (
  let rev = List.rev list in
  List.hd rev);;



let remove_last list = (
  let rev = List.rev list in        
  let rev_rest = List.tl rev in
  let rest = List.rev rev_rest in
  rest);;


let rec annotate_tail in_tp e = 
  match e with
  | Const'(x) -> e
  | Var'(x) -> e
  | If'(test, dit, dif) -> If'(annotate_tail false test, annotate_tail in_tp dit, annotate_tail in_tp dif)
  | Seq'(x) -> Seq'(annotate_tail_list in_tp x)
  | Set'(x,y) -> Set'(x, annotate_tail false y)
  | Def'(x,y) -> Def'(x, annotate_tail false y)
  | Or'(x) -> Or'(annotate_tail_list in_tp x)
  | LambdaSimple'(args, body) -> LambdaSimple'(args, annotate_tail true body)
  | LambdaOpt'(args, variadic, body) -> LambdaOpt'(args, variadic, annotate_tail true body)
  | Applic'(rator, rands) -> if (in_tp) then (ApplicTP'(annotate_tail false rator, List.map (annotate_tail false) rands))
                                     else (Applic'  (annotate_tail false rator, List.map (annotate_tail false) rands))
  | _ -> raise X_syntax_error


and annotate_tail_list in_tp list = (
    let last_arg = get_last_arg list in
    let rest = remove_last list in
    let output = (List.map (fun x -> annotate_tail false x) rest) @ [(annotate_tail in_tp last_arg)] in
    output);;
  
(*-------------------------------------------------------------------------------*)


(*----------------------------BOXING---------------------------------------------*)

let rec flat_seq list =(
  match list with
  | [] -> []
  | _ -> let car = List.hd list in
         let cdr = List.tl list in
            (match car with
            | Seq'(x) -> x @ (flat_seq cdr)
            | _ -> [car] @  (flat_seq cdr)
            )
);;

(* Update the lexical adress of the vars that need to be boxed
    as we dive in the scopes*)
let update_vars_indeces vars_to_box = (
    let update_var_index =(fun (x) ->
      (match x with
        | Var'(VarParam(v, minor)) -> Var'(VarBound(v,0,minor))
        | Var'(VarBound(v, major, minor)) -> Var'(VarBound(v,major+1,minor))
        | _ -> raise X_update_vars_indeces_error)
      ) in
    (match vars_to_box with 
      | [] -> vars_to_box
      | _ -> List.map update_var_index vars_to_box
    )
);;


let depth = ref 0 ;;

let rec box_annotate e vars_to_box =
  match e with
  | Const'(x) -> Const'(x)
  | Var'(x) ->(
      if (List.mem (Var'(x)) vars_to_box)
      then BoxGet'(x)
      else Var'(x))
  | If'(test,dit,dif) -> If'(box_annotate test vars_to_box, box_annotate dit vars_to_box, box_annotate dif vars_to_box)
  | Seq'(exprs) -> Seq'(List.map (fun (exp) -> box_annotate exp vars_to_box) exprs)
  | Set'(x,value) ->(
      let new_val = box_annotate value vars_to_box in
      if(List.mem (Var'(x)) vars_to_box)
      then BoxSet'(x,new_val)
      else Set'(x,new_val)
      )
  | Def'(x,y) ->(
    let v = box_annotate (Var'(x)) vars_to_box in  
    match v with 
    | Var'(z) -> Def'(z,box_annotate y vars_to_box)
    | _-> raise X_syntax_error
  )  
  | Or'(exprs) -> Or'(List.map (fun (exp) -> box_annotate exp vars_to_box) exprs)
  | LambdaSimple'(args,body) -> LambdaSimple'(args, box_lambda args body vars_to_box)
  | LambdaOpt'(args,variadic,body) -> LambdaOpt'(args, variadic, box_lambda (args@[variadic]) body vars_to_box)
  | Applic'(rator,rands) -> Applic'(box_annotate rator vars_to_box, List.map (fun (exp) -> box_annotate exp vars_to_box) rands) 
  | ApplicTP'(rator,rands) ->ApplicTP'(box_annotate rator vars_to_box, List.map (fun (exp) -> box_annotate exp vars_to_box) rands) 
  |_ -> raise X_syntax_error

(*add to vars_to_box all the vars that need to be boxed and change corresponding bodies*)
and box_lambda args body vars_to_box =(
  (*updates the indeces of the vars in the enviorment.*)
  let updated_vars = update_vars_indeces vars_to_box in
  (*adding vars that need to be boxed to vars_to_box*)
  let new_vars = need_to_box_list args 0 [] body in
  let new_vars_to_box = new_vars @ updated_vars in
  (*builds the new body recursivley*)
  let new_body = box_annotate body new_vars_to_box in

  (*Adding the set!.... in the beginning of the lambda, if needed.*)
  match new_vars with
  | [] -> new_body
  | _ -> (
    let sets = List.map (fun (x) -> 
    (match x with
    | Var'(VarParam(y,minor)) -> Set'(VarParam(y,minor), Box'(VarParam(y,minor)))
    | _ -> raise X_box_annotate_error 
    )) new_vars in
    Seq'(flat_seq(sets@[new_body])))
)



and update_var_index_ x = 
 (match x with
        | Var'(VarParam(v, minor)) -> Var'(VarBound(v,0,minor))
        | Var'(VarBound(v, major, minor)) -> Var'(VarBound(v,major+1,minor))
        | _ -> raise X_update_vars_indeces_error
 )



(*iterate over list and check for each member if it need to be boxed
 return a list of all the vars that need to be boxed in the list*)
and  need_to_box_list args minor vars_to_box body =(
  match args with
  | [] -> vars_to_box
  | first :: rest -> need_to_box_list rest (minor+1) (vars_to_box @ [Var'(VarParam(first,minor))]) body
);;



(*-------------------------------------------------------------------------------*)




let annotate_lexical_addresses e = handle_annot [] e;;

let annotate_tail_calls e = annotate_tail false e;;

let box_set e = box_annotate e [];;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)


