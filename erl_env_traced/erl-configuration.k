requires "erl-syntax.k"

module ERL-CONFIGURATION

  imports ERL-SYNTAX

  syntax BasicValue ::=  Atom | Int | Fun
  syntax Value ::=  BasicValue | "{" Values "}" | "[" Values "|" Value "]" | "[" Values "]"
  syntax Values ::= List{Value, ","}
  syntax Exception ::= "%badarith" | "%badarg" | "%badmatch" | "%badarity" | "%badfun" | "%undef"
  syntax Exp ::= Value
  syntax KResult ::= Value | Exception

  configuration <cfg color="yellow">
                  <k color="green"> $PGM:Pgm ~> $Exp </k>
                  <env color="red"> .Map </env>
                  <funVars> .Map </funVars>
                  <funEnv> .Map </funEnv>
                  <trace color="blue"> 

                    // BIFs
                    // "is_atom" |-> 0 // TODO: these have been not generated yet
                    // "is_boolean" |-> 0
                    // "is_integer" |-> 0
                    // "is_number" |-> 0
                    "hd" |-> 0
                    "tl" |-> 0
                    "element" |-> 0
                    "setelement" |-> 0
                    "tuple_size" |-> 0
                    "list_to_tuple" |-> 0
                    "tuple_to_list" |-> 0
                    "length" |-> 0

                    // Matching
                    "matches_and_restore" |-> 0
                    "matches_fun_and_restore" |-> 0
                    "matches" |-> 0
                    "matches_guard" |-> 0
                    "matches_fun" |-> 0

                    // erl.k
                    "lookup_var" |-> 0
                    "lookup_fun" |-> 0

                    "mult" |-> 0
                    "div" |-> 0
                    "div_ex" |-> 0
                    "rem" |-> 0
                    "rem_ex" |-> 0
                    "plus" |-> 0
                    "minus" |-> 0

                    "lt" |-> 0
                    "le" |-> 0
                    "lt_list" |-> 0
                    "ge" |-> 0
                    "gt" |-> 0
                    "or" |-> 0
                    "or_ex" |-> 0
                    "eq" |-> 0
                    "neq" |-> 0

                    "and" |-> 0
                    "and_ex" |-> 0
                    "andalso" |-> 0
                    "andalso_ex" |-> 0
                    "orelse" |-> 0
                    "orelse_ex" |-> 0
                    "not" |-> 0
                    "not_ex" |-> 0

                    "app" |-> 0
                    "app_ex" |-> 0
                    "diff" |-> 0
                    "diff_ex" |-> 0
                    "listcomp" |-> 0

                    "implicit_call" |-> 0
                    "recursive_call" |-> 0
                    "anon_call" |-> 0
                    "anon_call_badarity" |-> 0
                    "anon_call_var" |-> 0
                   // "mfa_call" |-> 0
                   // "fa_import_call" |-> 0
                    "fa_local_call" |-> 0
                    "fa_call_undef" |-> 0
                    "fa_call_badfun" |-> 0
                    "fa_call_badarity" |-> 0
                    "if" |-> 0
                    "case" |-> 0
                    "match" |-> 0
                    "begin_end" |-> 0
                  </trace>
                  <sideEffects> .List </sideEffects>
                  <currentMod> main </currentMod>
                  <funnames> .Set </funnames>
                  <mods>
                      <mod multiplicity="*">
                              <modname> .K </modname>
                              <fundefs color="blue"> .Map </fundefs>
                              <exports> .Set </exports>
                              <imports> .Set </imports>
                      </mod>
                  </mods>
                </cfg>
endmodule