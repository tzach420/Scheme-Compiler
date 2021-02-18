
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

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


  (*FUNCTIONS*)
let rec help_gcd a b =
  if b = 0 then a else gcd b (a mod b)

and gcd a b =
  let _gcd =help_gcd a b in
  if _gcd<0 then (-1)*_gcd
  else _gcd;;

let rec proper_list_of_list lst =
  match lst with
  | [] -> Nil
  | (x::y) -> Pair(x, proper_list_of_list y);;

  let rec improper x y =
    match x with
    | [] -> y
    | (z::w) -> Pair(z, improper w y);;
    
  let improper_list_of_list lst =
    match lst with
    | ((x, '.'), y) -> improper x y
    | _ -> raise X_no_match;;
    

(*PARSERS*)
let ascii_0 = int_of_char '0';;
let ascii_a = int_of_char 'a';;
let nt_division = char '/';;
let nt_zero = char '0';;
let nt_digit = range '0' '9';;

let remove_leading nt_left nt=
  let nt = caten nt_left nt in
  let nt = pack nt(function(_, e) -> e) in
  nt;;

let remove_leading_zeroes = remove_leading (star nt_zero);;

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let make_spaced nt =
  make_paired (star nt_whitespace) (star nt_whitespace) nt;;

(*let nt_natural = remove_leading_zeroes (plus nt_digit);;*)
let nt_natural = plus nt_digit;;

(*MAIN FUNCTION*)
let rec nt_sexp s =
  let nts = disj_list [nt_boolean;nt_char;nt_number;nt_string;nt_symbol;
           nt_list;nt_dotted_list;nt_quoted;nt_quasi_quoted;nt_unquoted;
           nt_unquote_and_spliced] in
  remove_comments nts s
(*COMMENTS*)
and nt_line_comment s =
  let prefix = char ';' in
  let chars = range (char_of_int 11) (char_of_int 127) in
  let comment = star chars in
  let end_line= char (char_of_int 10) in
  let nt = caten prefix comment in
  let nt = caten nt end_line in
  pack nt (fun x-> ' ') s

and nt_sexp_comment s =
  let prefix = word "#;" in
  let nt = caten prefix nt_sexp in
  pack nt (fun x-> ' ') s

and remove_comments nts s =
  let nt_spaces= pack nt_whitespace (fun x-> ' ') in
  let comments= disj_list[nt_line_comment;nt_sexp_comment;nt_spaces] in
  let comments= star comments in
  let nt = make_paired comments comments nts in
  nt s

(*BOOLEAN*)
and nt_boolean s = 
let nt_true = pack (word_ci "#t") (fun x-> Bool(true)) in
let nt_false = pack(word_ci "#f") (fun x-> Bool(false)) in 
disj nt_true nt_false s
  
(*CHARS*)
and nt_char s =
  let nt_visible_or_named = disj nt_named_char nt_visible_simple_char  in
  let nt = caten nt_char_prefix nt_visible_or_named in
  let nt = not_followed_by nt nt_symbol in
  pack nt (fun (x,y)->Char(y)) s
  
and nt_visible_simple_char s =
  range (char_of_int 33) (char_of_int 127) s

and nt_named_char s =
  let newline = pack (word_ci "newline") (fun x-> char_of_int 10) in
  let nul = pack (word_ci "nul") (fun x-> char_of_int 0) in
  let page = pack (word_ci "page") (fun x-> char_of_int 12) in
  let return = pack (word_ci "return") (fun x-> char_of_int 13) in
  let space = pack (word_ci "space") (fun x-> char_of_int 32) in
  let tab = pack (word_ci "tab") (fun x-> char_of_int 9) in
  disj_list[newline;nul;page;return;space;tab] s

and nt_char_prefix s=
  word "#\\" s

(*NUMBERS*)
and nt_number s =
  let integer_float_fraction =  disj_list[make_scientific;make_fraction;make_float;make_integer] in
  let nt= not_followed_by integer_float_fraction nt_symbol in
  pack nt (fun x-> Number(x)) s

and nt_integer s =
  let nt_plus = char '+' in
  let nt_minus = char '-' in
  let nt_plus_or_minus = disj nt_plus nt_minus in
  let nt_maybe = maybe nt_plus_or_minus in
  let nt = caten nt_maybe nt_natural in
  pack nt (function (x,y)->
    match x with
    | Some '+' -> '+' :: y
    | Some '-' -> '-' ::  y
    | None -> y
    | _ -> raise X_no_match) s

and make_integer s =
  pack nt_integer (fun x -> Fraction(int_of_string(list_to_string x),1)) s

and nt_fraction s =
  let slash = word "/" in
  let nt = caten_list [nt_integer; slash;nt_natural] in
  pack nt (fun (w) ->
  match w with
  | [x; y; z] ->
    let x = int_of_string(list_to_string(x)) in
    let z = int_of_string(list_to_string(z)) in
    let _gcd = gcd x z in
    let x = x /_gcd in
    let z = z/_gcd in
    [x,y,z] 
  | _-> raise X_no_match) s

and make_fraction s=
  pack nt_fraction ( fun(w) ->
  match w with
  | [x,y,z] -> Fraction(x, z)
  | _ -> raise X_no_match ) s

and nt_float s=
  let point = word "." in
  let naturals= plus nt_digit in
  let nt = caten_list [nt_integer; point;naturals] in
  pack nt (fun (x) -> List.concat x ) s

and make_float s=
  pack nt_float (fun x-> Float(float_of_string(list_to_string(x)))) s
  
and nt_scientific s=
  let integer_or_float = disj nt_float nt_integer  in
  let nt_e = char_ci 'e' in
  let nt_e = pack nt_e (fun x-> [x]) in
  caten_list [integer_or_float;nt_e;nt_integer] s

and make_scientific s=
  pack nt_scientific (fun (w)->
    match w with
    | [x; y; z] ->
      let x = float_of_string (list_to_string x) in
      let z = float_of_string (list_to_string z) in
      let w =  x*.(10.0**z) in
      Float(w)
    | _-> raise X_no_match ) s


(*STRINGS*)
and nt_string s=
  let start = char '\"' in
  let body = star nt_string_char in
  let start_body = caten start body in
  let nt = caten start_body start in 
  pack nt (fun ((x,y),z)-> String(list_to_string(y))) s
  
  and nt_string_char s =
    disj nt_string_meta_char nt_string_literal_char s

  and nt_string_literal_char s =
    let start= char '\"' in
    let backslash= char '\\' in
    let disj_start_back = disj start backslash in
    let nt = diff nt_any disj_start_back in
    pack nt (fun x-> x) s

  and nt_string_meta_char s =
    let return = pack (word "\\r") (fun x-> char_of_int 13) in
    let new_line = pack (word "\\n") (fun x-> char_of_int 10) in
    let tab = pack (word "\\t") (fun x-> char_of_int 9) in
    let page = pack (word "\\f") (fun x-> char_of_int 12) in
    let backslash = pack (word "\\\\") (fun x-> char_of_int 92) in
    let double_quote = pack (word "\\\"") (fun x-> char_of_int 34) in
    disj_list[return;new_line;tab;page;backslash;double_quote] s

  
    (*SYMBOLS*)
    and nt_symbol s =
    let plus_symbol_char = plus nt_symbol_char in
    let double_symbol_char = caten nt_symbol_char plus_symbol_char in
    let fix_double = pack double_symbol_char (fun (x,y)-> x::y) in
    let fix_no_dot = pack nt_symbol_char_no_dot (fun x-> [x]) in
    let nt = disj fix_double fix_no_dot in
    pack nt (fun (x)-> Symbol(list_to_string(x))) s

  and nt_symbol_char s =
    let nt_dot = char '.' in
    disj nt_symbol_char_no_dot nt_dot s

  and nt_symbol_char_no_dot s=
    let small_letters = range 'a' 'z' in
    let captial_letters = range 'A' 'Z' in
    let nt = disj small_letters captial_letters in
    let nt = pack nt (fun x-> lowercase_ascii x) in
    disj_list[nt_digit;nt;
    char '!';
    char '$';
    char '^';
    char '*';
    char '-';
    char '_';
    char '=';
    char '+';
    char '<';
    char '>';
    char '?';
    char '/';
    char ':'] s

(*LISTS*)
(*//proper list -> null at the end*)
and nt_list s = 
  let _sexp = make_spaced nt_sexp in
  let star_sexp = star _sexp in
  let nt = make_paired (char '(') (char ')') star_sexp in
  pack nt proper_list_of_list s

(*//improper list without null at the end*)
and nt_dotted_list s = 
  let _tail = make_spaced nt_sexp in 
  let _head = plus _tail in
  let _head = caten _head (make_spaced (char '.')) in
  let _pair = caten _head _tail in
  let nt = make_paired (char '(') (char ')') _pair in
  pack nt improper_list_of_list s

(*QUOTES*)
and make_quoted prefix name s =
  let no_space_sexp = make_spaced nt_sexp in
  let quoted = caten prefix no_space_sexp in
  pack quoted (fun (x,y) -> Pair(Symbol (name),Pair(y,Nil))) s

and nt_quoted s = make_quoted (char '\'') "quote" s
and nt_quasi_quoted s = make_quoted (char '`') "quasiquote" s 
and nt_unquoted s = make_quoted (char ',') "unquote" s
and nt_unquote_and_spliced s = 
  let prefix = word ",@" in
  let no_space_sexp = make_spaced nt_sexp in
  let quoted = caten prefix no_space_sexp in
  pack quoted (function (x,y) -> Pair(Symbol ("unquote-splicing"), Pair(y, Nil))) s;;

  module Reader: sig
    val read_sexprs : string -> sexpr list
  end
  = struct

  let normalize_scheme_symbol str =
    let s = string_to_list str in
    if (andmap
    (fun ch -> (ch = (lowercase_ascii ch)))
    s) then str
    else Printf.sprintf "|%s|" str;;


(*MAIN PARSER*)
let read_sexprs string =   
  let s = string_to_list string in
  let star_sexp = star nt_sexp in
  let (x,y) = star_sexp s in
  match x with
  | [] -> [Nil]
  | _-> x;;
  
end;; (* struct Reader *)
