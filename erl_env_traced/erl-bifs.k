requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-helpers.k"

module ERL-BIFS

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS

  rule <k> abs(I:Int) => absInt(I) ... </k>
       <trace> ... "abs" |-> (V' => V' +Int 1) ... </trace>
  rule <k> abs(_:Value) => %badarg ... </k>
       <trace> ... "abs_ex" |-> (V' => V' +Int 1) ... </trace> [owise]

  rule <k> is_atom(A:Atom) => true ... </k>
       <trace> ... "is_atom" |-> (V => V +Int 1) ... </trace>

  rule <k> is_atom(V:Value) => false ... </k>
       <trace> ... "is_atom" |-> (V' => V' +Int 1) ... </trace> 
    requires notBool (isAtom(V))



  rule <k> is_boolean(true) => true ... </k>
       <trace> ... "is_boolean" |-> (V => V +Int 1) ... </trace>

  rule <k> is_boolean(false) => true ... </k>
       <trace> ... "is_boolean" |-> (V => V +Int 1) ... </trace>

  rule <k> is_boolean(V:Value) => false ... </k>
       <trace> ... "is_boolean" |-> (V' => V' +Int 1) ... </trace>
    requires V =/=K true andBool V =/=K false

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
  
  rule <k> hd(_:Value) => %badarg ... </k>
       <trace> ... "hd_ex" |-> (V' => V' +Int 1) ... </trace> [owise]

  rule <k> tl(_:Value) => %badarg ... </k>
       <trace> ... "tl_ex" |-> (V' => V' +Int 1) ... </trace> [owise]

  rule <k> length([(.Exps)]) => 0 ... </k>
       <trace> ... "length" |-> (V' => V' +Int 1) ... </trace>
  rule <k> length([V:Value, (.Exps) | Vs]) => 1 + length(Vs) ... </k>
       <trace> ... "length" |-> (V' => V' +Int 1) ... </trace>
  rule <k> length(_:Value) => %badarg ... </k>
       <trace> ... "length_ex" |-> (V' => V' +Int 1) ... </trace> [owise]

  rule <k> element(I:Int, ({E, Es}):Value) => E ... </k>
       <trace> ... "element" |-> (V' => V' +Int 1) ... </trace>
    requires I ==K 1

  rule <k> element(I:Int, ({E, Es}):Value) => element(I -Int 1, {Es}) ... </k>
       <trace> ... "element" |-> (V' => V' +Int 1) ... </trace>
    requires I >Int 1
  
  rule <k> element(_:Value, _:Value) => %badarg ... </k>
       <trace> ... "element_ex" |-> (V' => V' +Int 1) ... </trace> [owise]

  rule <k> setelement(I:Int, ({Es}):Value, V:Value) => {setelement2(I, Es, V)} ... </k>
       <trace> ... "setelement" |-> (V' => V' +Int 1) ... </trace>  requires I >Int 0

  rule <k> setelement(_:Value, _:Value, _:Value) => %badarg ... </k>
       <trace> ... "setelement_ex" |-> (V' => V' +Int 1) ... </trace> [owise]

  syntax Exps ::= setelement2(Int, Exps, Value)
  rule setelement2(1, (E,Es), V) => V, Es
  rule setelement2(I, (E,Es), V) => E, setelement2(I -Int 1, Es, V)
  rule setelement2(I, .Exps, V) => %badarg

  rule <k> tuple_size({Exps}) => %count(Exps) ... </k>
       <trace> ... "tuple_size" |-> (V' => V' +Int 1) ... </trace>
  
  rule <k> tuple_size(_:Value) => %badarg ... </k>
       <trace> ... "tuple_size_ex" |-> (V' => V' +Int 1) ... </trace> [owise]

  syntax Exps ::= "#ErlListToKList" "(" Exp ")" [strict]
  rule #ErlListToKList( [ .Exps ] ) => .Exps
  rule #ErlListToKList( [ H, (.Exps) | T ] ) => H, #ErlListToKList( T )
  rule <k> list_to_tuple([L1 | L2]) => { #ErlListToKList([L1 | L2]) } ... </k>
       <trace> ... "list_to_tuple" |-> (V' => V' +Int 1) ... </trace>
  rule <k> list_to_tuple([.Exps]) => { .Exps } ... </k>
       <trace> ... "list_to_tuple" |-> (V' => V' +Int 1) ... </trace>
  rule <k> list_to_tuple(_:Value) => %badarg ... </k>
       <trace> ... "list_to_tuple_ex" |-> (V' => V' +Int 1) ... </trace>  [owise]

  syntax Exp ::= "#KListToErlList" "(" Exps ")" [strict]
  rule #KListToErlList( .Exps ) => [.Exps]
  rule #KListToErlList( E:Exp, Es:Exps ) => [ E | #KListToErlList( Es ) ]
  rule <k> tuple_to_list({ Es }) => #KListToErlList(Es) ...</k>
       <trace> ... "tuple_to_list" |-> (V' => V' +Int 1) ... </trace>
  rule <k> tuple_to_list(_:Value) => %badarg ...</k>
       <trace> ... "tuple_to_list_ex" |-> (V' => V' +Int 1) ... </trace> [owise]
  

endmodule
