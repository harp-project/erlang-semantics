requires "erl-syntax.k"
requires "erl-configuration.k"

module ERL-HELPERS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION

  // Returns the length of the expression list
  syntax Int ::= count(Exps)  [function]
  rule count(.Exps) => 0
  rule count(X:Exp,Xs:Exps) => ((count(Xs)) +Int 1)

  syntax Variable ::= parseVar(String) [function]
  rule parseVar(Str) => #parseToken("Variable", Str)

  syntax Set ::= fv(Exp) [function]
  rule fv(V:Variable) => SetItem(V)
  rule fv([H | T]) => fvs(H) fv(T)
  rule fv({T}) => fvs(T)
  rule fv(V:Value) => .Set

  syntax Set ::= fvs(Exps) [function]
  rule fvs(E:Exp, Es:Exps) => fv(E) fvs(Es)
  rule fvs(.Exps)  => .Set

  syntax RestoreEnv ::= restoreEnv(Map)
  syntax Exp ::= RestoreEnv
  rule <k> Val:KResult ~> restoreEnv(Orig) => Val ...</k>
       <env> Env => Orig </env>
  rule <k> restoreEnv(Orig) => . ...</k>
       <env> Env => Orig </env>

  syntax Exp ::= restoreAll(Map,Map,Map)
  rule <k> Val:KResult ~> restoreAll(Env0, FunVars0, FunEnv0) => Val ...</k>
       <env> Env => Env0 </env>
       <funVars> FunVars => FunVars0 </funVars>
       <funEnv> FunEnv => FunEnv0 </funEnv>
  rule <k> restoreAll(Env0, FunVars0, FunEnv0) => . ...</k>
       <env> Env => Env0 </env>
       <funVars> FunVars => FunVars0 </funVars>
       <funEnv> FunEnv => FunEnv0 </funEnv>

endmodule