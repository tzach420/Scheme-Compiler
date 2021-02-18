#use "reader.ml";;
open Reader;;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_expand_quasiquote_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)




(*----------------------FUNCTIONS--------------------------------*)



let rec make_new_letrec_body bindings body = (
  match bindings with 
  | Nil -> body
  | Pair(Pair(var, Pair(value, Nil)), cdr) -> Pair(Pair(Symbol("set!"), Pair(var, Pair(value, Nil))), make_new_letrec_body cdr body)
  | _ -> raise X_syntax_error
);;


let rec make_new_letrec_bindings bindings = (
  match bindings with 
  | Nil -> Nil
  | Pair(Pair(var, Pair(value, Nil)), cdr) -> Pair(Pair(var, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"),Nil)), Nil)), make_new_letrec_bindings cdr)
  | _ -> raise X_syntax_error
);;


let rec unique_list_of_sexp sexp_list list_to_return = 
  match sexp_list with
  | Nil -> list_to_return
  | Pair(Symbol x, y) -> 
          if (List.mem x list_to_return)
          then raise X_syntax_error 
          else unique_list_of_sexp y (List.append list_to_return [x]) 
  | Symbol(x) -> 
      if (List.mem x list_to_return) 
      then raise X_syntax_error 
      else List.append list_to_return [x] 
  | _ -> raise X_syntax_error;;

let remove_last lst = 
  let reversed = List.rev lst in
  let rev_tail = List.tl reversed in
  List.rev rev_tail;;


let rec is_proper_list sexpr = 
  match sexpr with
  | Nil -> true
  | Pair(a,b) -> is_proper_list b
  | _-> false;;

let rec get_last_arg list = 
  let list_length = List.length list in
  List.nth list (list_length-1);;


let expand_cond_1 test expr ribs = 
 let expr = (match expr with
              | Nil -> raise X_syntax_error
              | _ -> Pair(Symbol "begin", expr)) in
            (match ribs with
              | Nil -> Pair(Symbol "if", Pair(test, Pair(expr, Nil)))
              | _ -> Pair(Symbol "if", Pair(test, Pair(expr, Pair(Pair(Symbol "cond", ribs), Nil)))));;


let make_assignments test exprf rest =
  let value = Pair(Symbol("value"), Pair(test, Nil)) in 
  let f = Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(exprf, Nil))), Nil)) in
  let lambda_rest = Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Pair(Symbol("cond"), rest), Nil))), Nil)) in
  match rest with
    | Nil -> Pair(value, Pair(f, Nil))
    | _ ->   Pair(value, Pair(f, Pair(lambda_rest, Nil)));;


let make_body rest = 
  let exprf = Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)) in
  let dif = Pair(Pair(Symbol("rest"), Nil), Nil) in
  match rest with
    | Nil -> Pair(Symbol("if"), Pair(Symbol("value"), Pair(exprf, Nil)))
    | _ ->   Pair(Symbol("if"), Pair(Symbol("value"), Pair(exprf, dif)));;


let expand_cond_2 test exprf rest = 
  let assignments = make_assignments test exprf rest in
  let body = make_body rest in
  Pair(Symbol("let"),Pair(assignments, Pair(body, Nil)));;



(*1 - get let vars, 2- get let values *)
let rec get_let_variables bindings flag = 
  (match bindings with
    | Nil -> Nil
    | Pair(Pair(var, Pair(value, Nil)), rest) -> 
      (match flag with
      | 1 -> 
        (let args = get_let_variables rest 1 in
        (Pair(var, args)))
      | 2 -> 
        (let values = get_let_variables rest 2 in
        (Pair(value, values))) 
      | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error);;


let rec make_bindings_for_pset bindings = (
  match bindings with
  | Pair(Pair(Symbol(var),value),Nil) -> Pair(Pair(Symbol(String.uppercase_ascii var), value),Nil)
  | Pair(Pair(Symbol(var),value),cdr) -> Pair(Pair(Symbol(String.uppercase_ascii var), value),make_bindings_for_pset cdr)
  | _ -> raise X_syntax_error
);;

let rec make_body_for_pset bindings =(
   match bindings with
  | Pair(Pair(Symbol(var), Pair(y, Nil)),Nil) -> Pair(Pair(Symbol("set!"),Pair(Symbol(var),Pair(Symbol(String.uppercase_ascii var), Nil))), Nil)
  | Pair(Pair(Symbol(var),value),cdr) -> Pair(Pair(Symbol("set!"),Pair(Symbol(var),Pair(Symbol(String.uppercase_ascii var), Nil))), make_body_for_pset cdr)
  | _ -> raise X_syntax_error
);;

let rec flat_sequence list =(
  match list with
  | [] -> []
  | _ -> let car = List.hd list in
          let cdr = List.tl list in(
          match car with
          | Seq(x) -> x @ (flat_sequence cdr)
          | _ -> [car] @  (flat_sequence cdr)
          )
)

(*----------------------------------------------------------------*)

let rec tag_parse_exp exp =
match exp with

(*CONSTS*)
| Number(x) -> Const(Sexpr(Number(x)))
| Bool(x) -> Const(Sexpr(Bool(x)))
| Char(x) -> Const(Sexpr(Char(x)))
| String(x) -> Const(Sexpr(String(x)))
| Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))

(*Vars*)
| Symbol(x) -> 
  if (List.mem x reserved_word_list) then raise X_syntax_error else Var(x)

(*CONDITIONS*)
| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse_exp test, tag_parse_exp dit, tag_parse_exp dif)
| Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parse_exp test, tag_parse_exp dit, Const(Void))


(*Sequence*)
| Pair(Symbol("begin"), cdr) ->(
    match cdr with
    | Nil -> Const(Void)
    | Pair(x, Nil) -> tag_parse_exp x
    | _ -> Seq(flat_sequence (tag_parse_list cdr)))


(*Set*)  
| Pair(Symbol("set!"), Pair(Symbol(x), Pair(cdr, Nil))) ->
  Set(tag_parse_exp (Symbol(x)), tag_parse_exp cdr)

(*Define*)
| Pair(Symbol("define"), Pair(Symbol(x), Pair(cdr, Nil))) ->
   Def(tag_parse_exp (Symbol(x)), tag_parse_exp cdr)

(*Disjunctions*)
| Pair(Symbol("or"), cdr) ->(
    match cdr with
    | Nil -> Const(Sexpr(Bool false))
    | Pair(x,Nil) -> tag_parse_exp x
    | _ -> Or(tag_parse_list cdr))


(*Lambdas*)
| Pair(Symbol("lambda"), Pair(args, rest)) ->(
  let unique_args_list = unique_list_of_sexp args [] in
  if (is_proper_list args) then 
    (match rest with
    | Pair(x, Nil) -> LambdaSimple(unique_args_list, tag_parse_exp x)
    | _ ->  LambdaSimple(unique_args_list, Seq(flat_sequence (tag_parse_list rest))))                                           
  else 
    (match rest with
    | Pair(x, Nil) -> LambdaOpt(remove_last unique_args_list, get_last_arg unique_args_list, tag_parse_exp x)
    | _ -> LambdaOpt(remove_last unique_args_list, get_last_arg unique_args_list, Seq(flat_sequence (tag_parse_list rest))))
  )


(*-------------------------MACROS---------------------------------------*)

(*MIT Define*)
| Pair(Symbol("define"), Pair(Pair(Symbol(name), args), exprs)) ->
      let name = tag_parse_exp (Symbol(name)) in
      let proc = tag_parse_exp (Pair(Symbol("lambda"), Pair(args, exprs))) in
      Def(name, proc)

(*COND*)
| Pair(Symbol("cond"), ribs) ->
  (match ribs with
  | Pair(Pair(Symbol "else", x),_) -> tag_parse_exp (Pair(Symbol("begin"), x))
  | Pair(Pair(test, Pair(Symbol "=>", Pair(exprf, Nil))), rest) -> tag_parse_exp (expand_cond_2 test exprf rest )
  | Pair(Pair(test, expr), rest) -> tag_parse_exp (expand_cond_1 test expr rest)
  | _ ->raise X_syntax_error)

(*LET*)
| Pair(Symbol("let"), Pair(bindings, body)) ->  
  let variables = get_let_variables bindings 1 in
  let values = get_let_variables bindings 2 in
  let l_body = (match body with
                    | Pair(x,Nil) -> tag_parse_exp x
                    | _ -> Seq(flat_sequence (tag_parse_list body))) in
  Applic(LambdaSimple((unique_list_of_sexp variables []), l_body), (tag_parse_list values))

(*LET**)
| Pair(Symbol("let*"), Pair(bindings, body)) ->
 (match bindings with
 | Nil -> tag_parse_exp (Pair(Symbol("let"),Pair(bindings,body)))
 | Pair(Pair(var,Pair(value,Nil)),Nil) -> tag_parse_exp (Pair(Symbol("let"), Pair(bindings,body)))
 | Pair(Pair(var,Pair(value,Nil)), cdr)-> 
    let first =  Pair(Pair(var, Pair(value, Nil)),Nil) in
    let new_body = Pair(Pair(Symbol("let*"), Pair(cdr, body)),Nil) in
    let new_expr = Pair(Symbol("let"),Pair(first, new_body)) in
    tag_parse_exp new_expr
 |_ -> raise X_syntax_error
 )

 (*LET-REC*)
| Pair(Symbol("letrec"),Pair(bindings, body)) ->
  (match bindings with
  | Nil -> tag_parse_exp (Pair(Symbol("let"),Pair(bindings,body)))
  | Pair(Pair(var, Pair(value, Nil)), cdr) -> 
    let new_bindings = make_new_letrec_bindings bindings in
    let new_body = make_new_letrec_body bindings body in
    tag_parse_exp (Pair(Symbol("let"), Pair(new_bindings, new_body)))
  | _ -> raise X_syntax_error
  )


(*AND*)
| Pair(Symbol("and"), cdr) -> expand_and cdr

(*QUASIQUOTE*)
| Pair(Symbol("quasiquote"), Pair(list, Nil)) -> tag_parse_exp (expand_quasiquote list)

(*PSET*)
| Pair(Symbol("pset!"),bindings) -> tag_parse_exp (expand_pset bindings)

(*APPLIC*)
| Pair(proc, args) -> Applic(tag_parse_exp proc, tag_parse_list args)

| _ -> raise X_syntax_error

(*------------------------HELP FUNCTIONS-------------------------------------------------*)


and expand_pset bindings = (
  let new_bindings=  make_bindings_for_pset bindings in
  let body = make_body_for_pset bindings in
  Pair(Symbol("let"), Pair(new_bindings, body))
)


and expand_quasiquote list= (
  match list with
  | Pair(Symbol("unquote"),Pair(sexpr,Nil)) ->  sexpr
  | Pair(Symbol("unquote-splicing"), Pair(sexpr,Nil)) -> raise X_syntax_error
  | Nil -> Pair((Symbol("quote")), Pair(Nil, Nil))
  | Symbol(x) -> Pair(Symbol("quote"), Pair(Symbol(x),Nil)) 
  | Pair(a,b) ->
    (match a with
      | Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)) -> Pair(Symbol("append"), Pair(sexpr, Pair(expand_quasiquote b, Nil)))
      | _ -> Pair(Symbol("cons"), Pair(expand_quasiquote a, Pair(expand_quasiquote b, Nil)))
    )
  | _ -> list
)

and tag_parse_list list =(
  match list with
  | Nil -> []
  | Pair(x, y) -> (tag_parse_exp x)::(tag_parse_list y)
  | _ -> raise X_syntax_error)


and expand_and list = (
    match list with
    | Nil -> Const(Sexpr(Bool(true)))
    | Pair(x,Nil) -> tag_parse_exp x
    | Pair(x,cdr) -> If(tag_parse_exp x, expand_and cdr,Const(Sexpr(Bool(false))))
    |_-> raise X_syntax_error
);;


let tag_parse_expressions sexpr = List.map tag_parse_exp sexpr;;


let test value =
  let sexpr_list= read_sexprs value in
  tag_parse_expressions sexpr_list;;

  
end;; (* struct Tag_Parser *)

