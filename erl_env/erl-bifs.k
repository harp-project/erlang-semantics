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

  rule hd(_:Value) => %badarg  [owise]

  rule tl(_:Value) => %badarg  [owise]

  rule length([(.Exps)]) => 0
  rule length([V:Value, (.Exps) | Vs]) => 1 + length(Vs)
  rule length(_:Value) => %badarg  [owise]

  rule element(I:Int, ({E, Es}):Value) => E requires I ==K 1
  rule element(I:Int, ({E, Es}):Value) => element(I -Int 1, {Es}) requires I >Int 1
  rule element(_:Value, _:Value) => %badarg  [owise]

  rule setelement(I:Int, ({Es}):Value, V:Value) => {setelement2(I, Es, V)} requires I >Int 0
  rule setelement(_:Value, _:Value, _:Value) => %badarg  [owise]

  syntax Exps ::= setelement2(Int, Exps, Value)
  rule setelement2(1, (E,Es), V) => V, Es
  rule setelement2(I, (E,Es), V) => E, setelement2(I -Int 1, Es, V)
  rule setelement2(I, .Exps, V) => %badarg

  rule tuple_size({Exps}) => %count(Exps)
  rule tuple_size(_:Value) => %badarg   [owise]

  syntax Exps ::= "#ErlListToKList" "(" Exp ")" [strict]
  rule #ErlListToKList( [ .Exps ] ) => .Exps
  rule #ErlListToKList( [ H, (.Exps) | T ] ) => H, #ErlListToKList( T )
  rule #ErlListToKList( [Es:Exps] ) => #ErlListToKList( [Es | [.Exps]] ) requires Es =/=K .Exps     // List normalisation
  rule #ErlListToKList( [E:Exp,Es | T] ) => #ErlListToKList( [E | [Es|T]] ) requires Es =/=K .Exps  // List normalisation
  rule list_to_tuple([L1 | L2]) => { #ErlListToKList([L1 | L2]) }
  rule list_to_tuple([.Exps]) => { .Exps }
  rule list_to_tuple(_:Value) => %badarg  [owise]

  syntax Exp ::= "#KListToErlList" "(" Exps ")" [strict]
  rule #KListToErlList( .Exps ) => [.Exps]
  rule #KListToErlList( E:Exp, Es:Exps ) => [ E | #KListToErlList( Es ) ]
  rule tuple_to_list({ Es }) => #KListToErlList (Es)
  rule tuple_to_list(_:Value) => %badarg  [owise]
  
  // rule tuple_to_list({ Es }) => [ Es ]      // After using this rule, list normalisation does not apply
  

endmodule
