# Scheme-Compiler
Implementation of Scheme compiler. Written in Ocaml.
The compiler takes a scheme source code (file written in Scheme), 
converts it to assembly and creates executable file to run (file written in Assembly).

# Table of contents
<!--ts-->
   * [Compiler pipeline](#Compiler-pipeline)
   * [The Reader](#The-Reader)
   * [The Tag Parser](#The-Tag-Parser)
      *[Core forms] (#Core-forms)
      *[Constants] (#Constants)
   * [The Semantic Analyzer](#The-Semantic-Analyzer)
   * [The Code Generator](#The-Code-Generation)
   * [Compile](#Compilation)
<!--te-->

Compiler pipeline
=========
 <img src="./img/pipeline.png"><br/>


The Reader
=========
The reader is a parser for extended S-expressions: It reads text from a string, and outputs an abstract syntax tree for extended S-expressions.
This procedure takes a string, assuming it contains any number of sexprs, and returns a list of abstract syntax trees that correctly represent the input. Such ASTs are represented by the sexpr type defined in reader.ml.

The Tag Parser
=========

Core forms
-----
This is the expr type which defines the abstract syntax of scheme expressions:
type expr =
| Const of constant
| Var of string
| If of expr * expr * expr | Seq of expr list
| Set of expr * expr
| Def of expr * expr
| Or of expr list
| LambdaSimple of string list * expr
| LambdaOpt of string list * string * expr | Applic of expr * (expr list)

type constant =
| Sexpr of sexpr | Void

Constants
-----
Constants come in two forms: quoted and unquoted. The field of any quoted form is a constant. Self-evaluating forms (Booleans, chars, numbers, strings) are constants too, even if they haven’t been quoted.
