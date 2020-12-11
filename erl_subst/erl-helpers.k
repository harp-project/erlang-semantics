requires "erl-syntax.k"
requires "erl-configuration.k"

module ERL-HELPERS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION

  // Returns the number of expressions from an expression list
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

endmodule