requires "erl-syntax.k"

module ERL-CONFIGURATION

  imports ERL-SYNTAX

  syntax BasicValue ::=  Atom | Int | Fun
  syntax Value ::=  BasicValue | "{" Values "}" | "[" Values "|" Value "]" | "[" Values "]"
  syntax Values ::= List{Value, ","}
  syntax Exception ::= "%badarith" | "%badarg" | "%badmatch" | "%badarity" | "%badfun" | "%undef"
  syntax Exp ::= Value
  syntax KResult ::= Value

  configuration <cfg color="yellow">
                  <k color="green"> $PGM:Pgm ~> $Exp </k>
                  <env color="red"> .Map </env>
                  <funVars> .Map </funVars>
                  <funEnv> .Map </funEnv>
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