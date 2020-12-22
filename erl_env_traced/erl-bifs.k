requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-helpers.k"

module ERL-BIFS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS

  rule <k> is_atom(A:Atom) => true ... </k>
       <trace> ... "is_atom" |-> (V => V +Int 1) ... </trace>

  rule <k> is_atom(V:Value) => false ... </k>
       <trace> ... "is_atom" |-> (V' => V' +Int 1) ... </trace> 
    requires notBool (isAtom(V))

//  rule <k> is_atom( %Exc V ) => %Exc V </k>
//       <trace> ... "is_atom_ex" |-> (V => V +Int 1) ... </trace>



  rule <k> is_boolean(true) => true ... </k>
       <trace> ... "is_boolean" |-> (V => V +Int 1) ... </trace>

  rule <k> is_boolean(false) => true ... </k>
       <trace> ... "is_boolean" |-> (V => V +Int 1) ... </trace>

  rule <k> is_boolean(V:Value) => false ... </k>
       <trace> ... "is_boolean" |-> (V' => V' +Int 1) ... </trace>
    requires V =/=K true andBool V =/=K false

//  rule <k> is_boolean(E:Exception) => true </k>
//       <trace> ... "is_boolean" |-> (V => V +Int 1) ... </trace>

  rule <k> is_integer(I:Int) => true ... </k>
       <trace> ... "is_integer" |-> (V' => V' +Int 1) ... </trace>
  rule <k> is_integer(V:Value) => false ... </k>
       <trace> ... "is_integer" |-> (V' => V' +Int 1) ... </trace>
    requires notBool (isInt(V)) 

  rule <k> is_number(I:Int) => true ... </k>
       <trace> ... "is_number" |-> (V' => V' +Int 1) ... </trace>
  rule <k> is_number(V:Value) => false ... </k>
       <trace> ... "is_number" |-> (V' => V' +Int 1) ... </trace>
    requires notBool (isInt(V))

  rule <k> hd([V:Value, (.Exps) | _]) => V ... </k>
       <trace> ... "hd" |-> (V' => V' +Int 1) ... </trace>

  rule <k> tl([_ | Xs:Value]) => Xs ... </k>
       <trace> ... "tl" |-> (V' => V' +Int 1) ... </trace>

  rule <k> length([(.Exps)]) => 0 ... </k>
       <trace> ... "length" |-> (V' => V' +Int 1) ... </trace>
  rule <k> length([V:Value, (.Exps) | Vs]) => 1 + length(Vs) ... </k>
       <trace> ... "length" |-> (V' => V' +Int 1) ... </trace>

  rule <k> element(I:Int, ({E, Es}):Value) => E ... </k>
       <trace> ... "element" |-> (V' => V' +Int 1) ... </trace>
    requires I ==K 1

  rule <k> element(I:Int, ({E, Es}):Value) => element(I -Int 1, {Es}) ... </k>
       <trace> ... "element" |-> (V' => V' +Int 1) ... </trace>
    requires I =/=K 1

  rule <k> setelement(I:Int, ({Es}):Value, V:Value) => {setelement2(I, Es, V)} ... </k>
       <trace> ... "setelement" |-> (V' => V' +Int 1) ... </trace>

  syntax Exps ::= setelement2(Int, Exps, Value)
  rule setelement2(1, (E,Es), V) => V, Es
  rule setelement2(I, (E,Es), V) => E, setelement2(I -Int 1, Es, V)

  rule <k> tuple_size({Exps}) => %count(Exps) ... </k>
       <trace> ... "tuple_size" |-> (V' => V' +Int 1) ... </trace>

  syntax Exps ::= "#ErlListToKList" "(" Exp ")" [strict]
  rule #ErlListToKList( [ .Exps ] ) => .Exps
  rule #ErlListToKList( [ H, (.Exps) | T ] ) => H, #ErlListToKList( T )
  rule #ErlListToKList( [Es:Exps] ) => #ErlListToKList( [Es | [.Exps]] ) requires Es =/=K .Exps     // List normalisation
  rule #ErlListToKList( [E:Exp,Es | T] ) => #ErlListToKList( [E | [Es|T]] ) requires Es =/=K .Exps  // List normalisation
  rule <k> list_to_tuple(L) => { #ErlListToKList(L) } ... </k>
       <trace> ... "list_to_tuple" |-> (V' => V' +Int 1) ... </trace>

  /* syntax Exp ::= "#KListToErlList" "(" Exps ")" [function]
  rule #KListToErlList( .Exps ) => [.Exps]
  rule #KListToErlList( E:Exp ) => [E]
  rule #KListToErlList( E:Exp, Es:Exps ) => [ E | #KListToErlList( Es ) ]
  rule tuple_to_list(({ Es },.Exps)) => #KListToErlList (Es) */
  
  rule <k> tuple_to_list({ Es }) => [ Es ] ... </k>     // After using this rule, list normalisation does not apply
       <trace> ... "tuple_to_list" |-> (V' => V' +Int 1) ... </trace>
  

endmodule
