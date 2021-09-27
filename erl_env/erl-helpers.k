requires "erl-syntax.k"
requires "erl-configuration.k"

module ERL-HELPERS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION

  // Returns the length of the expression list
  syntax Int ::= "%count" "(" Exps ")"  [function]
  rule %count(.Exps) => 0
  rule %count(_,Xs:Exps) => ((%count(Xs)) +Int 1)

  syntax Set ::= fv(Exp) [function]
  rule fv(V:Variable) => SetItem(V)
  rule fv([H | T]) => fvs(H) fv(T)
  rule fv({T}) => fvs(T)
  rule fv(_:Value) => .Set

  syntax Set ::= fvs(Exps) [function]
  rule fvs(E:Exp, Es:Exps) => fv(E) fvs(Es)
  rule fvs(.Exps)  => .Set

  syntax RestoreEnv ::= restoreEnv(Map)
  syntax Exp ::= RestoreEnv
  rule <k> Val:KResult ~> restoreEnv(Orig) => Val ...</k>
       <env> _ => Orig </env>
  rule <k> restoreEnv(Orig) => . ...</k>
       <env> _ => Orig </env>

  syntax Exp ::= restoreAll(Map,Map,Map)
  rule <k> Val:KResult ~> restoreAll(Env0, FunVars0, FunEnv0) => Val ...</k>
       <env> _ => Env0 </env>
       <funVars> _ => FunVars0 </funVars>
       <funEnv> _ => FunEnv0 </funEnv>
  rule <k> restoreAll(Env0, FunVars0, FunEnv0) => . ...</k>
       <env> _ => Env0 </env>
       <funVars> _ => FunVars0 </funVars>
       <funEnv> _ => FunEnv0 </funEnv>

endmodule
