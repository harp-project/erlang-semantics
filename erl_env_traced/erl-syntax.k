/*
\title{Erlang semantics}
\author{Judit H. Koszegi
        (\texttt{\koszegijudit@elte.hu})}
\organization{University of Kent, Eotvos Lorand University}
*/

//@ \section{Syntax}

module ERL-SYNTAX

//==============================================================================
// Tokens

  syntax UnquotedAtom ::= Token{[a-z][\_a-zA-Z0-9\@]*}
         [notInRules, autoReject, token, regex([a-z][\_a-zA-Z0-9\@]*)]

  syntax QuotedAtom ::= Token{[\'][\_a-zA-Z0-9\@]*[\']}
         [notInRules, autoReject, token, regex([\'][\_a-zA-Z0-9\@]*[\'])]

  syntax Atom ::= UnquotedAtom | QuotedAtom | Bool

  syntax BIF ::= "is_atom" | "is_boolean" | "is_integer" | "is_number" |
              // "is_function" | "is_list" | "is_tuple" | TODO
                 "hd" | "tl" | "length" |
                 "element" | "setelement" | "tuple_size" |
                 "list_to_tuple" | "tuple_to_list" [token]
  syntax Atom ::= BIF

  syntax Joker ::= "_" [notInRules, token, joker]

  syntax Variable ::= Token{[\_A-Z][\_a-zA-Z0-9\@]*}
         [notInRules, autoReject, token, regex([\_A-Z][\_a-zA-Z0-9\@]*)]

  syntax Variable ::= Joker

//==============================================================================
// Expressions

  syntax Exp ::=  Atom | Int | Variable //| "[" "]"

  // TODO: add more operators
  syntax Exp ::= "not" Exp                    [strict, arith]
               > left:
                 Exp "*" Exp                  [strict, arith]
               | Exp "div" Exp                [strict, arith]
               | Exp "rem" Exp                [strict, arith]
               | Exp "and" Exp                [seqstrict, arith]
               > left:
                 Exp "+" Exp                  [strict, arith]
               | Exp "-" Exp                  [strict, arith]
               | Exp "or" Exp                 [seqstrict, arith]
               > right:
                 Exp "++" Exp                 [strict, arith]
               | Exp "--" Exp                 [strict, arith]
               > non-assoc:
                 Exp "<" Exp                  [strict, arith]
               | Exp "=<" Exp                 [strict, arith]
               | Exp ">" Exp                  [strict, arith]
               | Exp ">=" Exp                 [strict, arith]
               | Exp "==" Exp                 [strict, arith]
               | Exp "/=" Exp                 [strict, arith]
               > left:
                 Exp "andalso" Exp            [strict(1), arith, prefer] //it is non-assoc in the manual
               > left:
                 Exp "orelse" Exp             [strict(1), arith, prefer] //it is non-assoc in the manual

  syntax Exp ::= "{" Exps "}"                 [strict,    tuple]
               | "[" Exps "]"                 [strict,    list]
               | "[" Exps "|" Exp "]"         [seqstrict, list]
               | "[" Exp "||" GFs "]"         [listcomp]
               | Exp "(" Exps ")"             [seqstrict, funcall]
               | Exp ":" Exp "(" Exps ")"     [seqstrict, mfacall]
               | "case" Exp "of" Match "end"  [strict(1), case]
               | "if" IfBody "end"            [if]
               | "begin" Exps "end"           [           block] //TODO: allow the "begin" - "end" be omitted in unambiguous context
               | MatchExp
               | Fun
               | "(" Exp ")"                  [bracket]

  syntax Exps ::= List{Exp, ","}              [strict]

  syntax MatchExp ::= Exp "=" Exp             [strict(2), matchexpr]
  syntax Fun      ::= "fun" Clauses "end"     [fun]
                    | "fun" Exp"/"Exp         [strict, fun] //TODO: allow only atom or var and int or var

  syntax GuardSeq ::= List{Exps, ";"}  // TODO: allow only valid guards instead of arbitrary expressions

  syntax Match0 ::= Exp "->" Exps  [klabel("_->_::Match0")]
                  | Exp "when" GuardSeq "->" Exps
  syntax Match  ::= List{Match0, ";"}

  syntax IfCl   ::= GuardSeq "->" Exp            [ifcl]
  syntax IfBody ::= List{IfCl, ";"}

  syntax Clause0     ::= "("Exps")" "->" Exps  [clause]  //TODO: allow optional when
  syntax NamedClause ::=  Variable "("Exps")" "->" Exps  [nclause]
  syntax Clause      ::= Clause0 | NamedClause
  syntax Clauses     ::= List{Clause, ";"}

  syntax Filter      ::= Exp
  syntax Generator   ::= Exp "<-" Exp
  syntax GF          ::= Filter | Generator
  syntax GFs         ::= List{GF, ","}

//==============================================================================
// Forms

//----------------------------------------------------------------------------
// Module Attributes

  syntax ModuleAttrib ::= "-" "module" "(" Atom ")" "." [mattrib]
  syntax ExportAttrib ::= "-" "export" "(" NameArityList ")" "."
  syntax ImportAttrib ::= "-" "import" "(" Atom "," NameArityList ")" "."
  // TODO other attribs

  syntax Attrib ::= ExportAttrib | ImportAttrib [attrib]
  syntax Attribs ::= List{Attrib, ""}

  syntax NameArity   ::= Atom "/" Int
  syntax NameArities ::= NameArity | NameArity "," NameArities [right]
  syntax NameArityList ::= "[" NameArities "]"

//----------------------------------------------------------------------------
// Function Definitions

  // TODO: optional when; check whether the different clauses have the same ariry
  syntax FunCl0  ::= Atom"("Exps")" "->" Exps ";" [funcl0]
  syntax FunCl1  ::= Atom"("Exps")" "->" Exps "." [funcl1]
  syntax FunCl   ::= FunCl0 | FunCl1

  syntax FunDefs ::= FunCl | FunDefs FunDefs [right]

//----------------------------------------------------------------------------
// Module

   syntax Module ::= ModuleAttrib Attribs FunDefs
   syntax Modules ::= Module | Module Modules [right]

//==============================================================================
// Priorities

  syntax priorities
                     mattrib > attrib
                   > funcl1 > funcl0
                   > fun
                   > mfacall
                   > funcall
                   > tuple
                   > listcomp
                   > list
                   > block
                   > case  > if
                   > arith
                   > matchexpr
                   > nclause > clause


//==============================================================================
// Program (start symbol)

  syntax Pgm ::= Modules | Exp

  syntax Atom ::= "main" [token]

//==============================================================================
// Tokens for verification

  syntax Variable ::= "Xx" | "Yy" | "Zz" | "Aa" | "Bb" | "Cc" | "Sum" | "Num" [token]
  syntax Atom     ::= "x" | "f" | "g" | "sum" | "rec" [token]      
 
endmodule
