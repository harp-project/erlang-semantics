requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-helpers.k"

module ERL-BIFS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS

  rule is_atom(A:Atom) => true
  rule is_atom(V:Value) => false requires notBool (isAtom(V))

  rule is_boolean(true) => true
  rule is_boolean(false) => true
  rule is_boolean(V:Value) => false requires V =/=K true andBool V =/=K false

  rule is_integer(I:Int) => true
  rule is_integer(V:Value) => false requires notBool (isInt(V))

  rule is_number(I:Int) => true
  rule is_number(V:Value) => false requires notBool (isInt(V))

  rule hd([V:Value, (.Exps) | _]) => V

  rule tl([_ | Xs:Value]) => Xs

  rule length([.Exps]) => 0
  rule length(([E | Es]):Value) => 1 + length(Es)

  rule element(I:Int, ({E, Es}):Value) => E requires I ==K 1
  rule element(I:Int, ({E, Es}):Value) => element(I -Int 1, {Es}) requires I =/=K 1

  rule setelement(I:Int, ({Es}):Value, V:Value) => {setelement2(I, Es, V)}

  syntax Exps ::= setelement2(Int, Exps, Value)
  rule setelement2(1, (E,Es), V) => V, Es
  rule setelement2(I, (E,Es), V) => E, setelement2(I -Int 1, Es, V)

  rule tuple_size({Exps}) => count(Exps)

endmodule