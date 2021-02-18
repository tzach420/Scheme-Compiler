# Scheme-Compiler
Implementation of Scheme compiler. Written in Ocaml.
The compiler takes a scheme source code (file written in Scheme), 
converts it to assembly and creates executable file to run (file written in Assembly).

# Table of contents
<!--ts-->
   * [Compiler pipeline](#Compiler-pipeline)
   * [The Reader](#The-Reader)
   * [The Tag Parser](#The-Tag-Parser)
      * [Core forms](#Core-forms)
      	* [Constants](#Constants)
	    * [Variables](#Variables)
	    * [Conditionals](#Conditionals)
	    * [Sequences](#Sequences)
	    * [Assignments](#Assignments)
	    * [Definitions](#Definitions)
	    * [Disjunctions](#Disjunctions)
	    * [Lambda Expressions](#Lambda-Expressions)
	  * [Macro expansions](#Macro-expansions)
	    * [Quasiquoted expressions](#Quasiquoted-expressions)
	    * [Cond expressions](#Cond-expressions)
	    * [Let expressions](#Let-expressions)
	    * [Let* expressions](#Let*-expressions)
	    * [LetRec expressions](#LetRec-expressions)
	    * [And expressions](#And-expressions)
	    * [MIT define expressions](#MIT-define-expressions)
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

The tag-parser converts from the AST of sexprs to the AST of expressions, and performs macro- expansions along the way. Such ASTs are represented by the expr type defined in tag-parser.ml.

## Core forms
----

This is the expr type which defines the abstract syntax of scheme expressions:
type expr =
| Const of constant
| Var of string
| If of expr * expr * expr
| Seq of expr list
| Set of expr * expr
| Def of expr * expr
| Or of expr list
| LambdaSimple of string list * expr
| LambdaOpt of string list * string * expr | Applic of expr * (expr list)

type constant =
| Sexpr of sexpr | Void

### Constants

Constants come in two forms: quoted and unquoted. The field of any quoted form is a constant. Self-evaluating forms (Booleans, chars, numbers, strings) are constants too, even if they haven’t been quoted.

### Variables

The concrete syntax of variables is given as unquoted symbols that are not reserved words. For each variable instance of Variable is generated.

### Conditionals

Support both the if-then & if-then-else forms of conditions in Scheme (If). If-then forms expand into if-then-else forms, where the else field has the value Const (Void).

### Sequences
There are two kinds of sequences of expressions: explicit, and implicit. Explicit sequences are proper lists in which the symbol begin is the first element. Implicit sequences of expressions appear in various special forms, such as cond, lambda, let, etc. Both kinds of sequences will be parsed using the Seq type constructor.
Similar to the handling of or and and forms, tag-parsed sequences have two base forms which differ from the general tag-parsed form:
-An empty sequence should be tag-parsed to Const Void.
-A sequence with a single element should not be tag-parsed as a sequence.
An expr should not contain nested sequences (neither explicit nor implicit), such sequences should be flattened into a single sequence.

### Assignments
Assignments are written using set!-expressions (Set) or pset!-expressions. set!-expressions are core-forms that supported by using the type constructor Set. pset!-expressions are supported using macro-expansions (as explained further below).

### Definitions
There are two ways to write definitions in Scheme: The basic way, and “the MIT-syntax for define”, which is used to define procedures, and which appears throughout the book The Structure and Interpretation of Computer Programs. Simple define expressions are considered core forms (Def) while MIT define expressions will be treated as macros.

### Disjunctions
Disjunctions are simply or-expressions (Or). We shall be supporting
or-expressions as a core form, while macro-expanding and-expressions.

### Lambda Expressions
There are 3 kinds of λ-expressions in Scheme: simple, with optional arguments and variadic. We will be using two forms to represent these three different λ- expressions: LambdaSimple of string list * expr and LambdaOpt of string list * string * expr. Variadic λ-expressions are represented as LambdaOpt structures with an empty list of required parameters. The body of a lambda-expression is an implicit sequence.

## Macro expansions
----

### Quasiquoted expressions
Upon recognizing a quasiquoted-expression, we will expand the expression while considering unquote and unquote-splicing subexpressions. After performing the initial expansion, we will call the tag-parser recursively over the expanded form.
we should not support nested quasiquote-expressions.

### Cond expressions
We will expand cond-expressions, while supporting 3 types of ribs. The tag-parser should be called recursively over the expanded form. A cond without an else rib returns Const (Void) if none of the tests match (this required should be automatically covered by the expansion of if-then to if-then-else). In addition, cond ribs of type 1 and of type 3 contain implicit sequence of expressions.

### Let expressions
We will expand these into applications, and call the tag-parser recursively.

### Let* expressions
We will Expand these into nested let expressions, and call the tag-parser recursively.

### LetRec expressions
We will Expand these into let-expressions with assignmentes, and call the tag-parser recursively.

### And expressions
We will Expand these into nested if-expressions, and call the tag-parser recursively.

### MIT define expressions
MIT-style define-expressions have the form (define (<name> . <argl>) . (<expr> +)), where:
- <name> is the name of the variable
- <argl> represents the list of parameters
- <expr> + is a non-empty sequence of expressions
The MIT-style define-expression should be macro-expanded into a simple define-expression containing the relevant lambda form. The tag-parser should be called recursively over the expanded form.


