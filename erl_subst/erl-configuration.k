requires "erl-syntax.k"

module ERL-CONFIGURATION

  imports ERL-SYNTAX

  syntax BasicValue ::=  Atom | Int | Fun
  syntax Value ::=  BasicValue | "{" Values "}" | "[" Values "|" Value "]" | "[" Values "]"
  syntax Values ::= List{Value, ","}
  syntax Exp ::= Value
  syntax KResult ::= Value

  configuration <cfg color="yellow">
                  <k color="green"> $PGM:Pgm ~> $Exp:Exp </k>
                  <funvars color="red"> .Map </funvars>
                  <currentmod> main </currentmod>
                  <mods>
                      <mod multiplicity="*">
                              <modName> .K </modName>
                              <defs color="blue"> .Map </defs>
                              <exports> .Set </exports>
                              <imports> .Set </imports>
                      </mod>
                  </mods>
                </cfg>
endmodule