requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-substitution.k"

module ERL-MATCHING

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-SUBSTITUTION

  // The resulted map of getMatching function contains this key
  // when the maching is unsuccesful.
  syntax Atom ::= "badmatch" [token]

  syntax Exp ::= matches(Exp, Match)

  // Without guards
  rule matches(Exp, P -> E) => badmatch
      requires notBool (isMatching(Exp, P))
  rule matches(Exp, (P -> E ; Ms)) => subst(E, getMatching(Exp, P))
      requires isMatching(Exp, P)
  rule matches(Exp, (P -> E ; Ms)) => matches(Exp, Ms)
      requires (notBool (isMatching(Exp, P))) andBool (Ms =/=K .Match)

  // With guards
  // TODO: when we will have exceptions: exception means false

  rule matches(Exp, (P when G:GuardSeq -> E ; Ms)) =>
       subst(transformGS(G), getMatching(Exp, P)) ~> matches(Exp, (P when HOLE -> E ; Ms))
      requires (isValue(G) =/=K true) andBool (isMatching(Exp, P))
      // [heat]

  rule G:Value ~> matches(Exp, (P when HOLE -> E ; Ms)) => matches(Exp, (P when G -> E ; Ms))
      // [cool]

  rule matches(Exp, (P when true -> E ; Ms)) => subst(E, getMatching(Exp, P))
  rule matches(Exp, (P when V:Value -> E ; Ms)) => matches(Exp, Ms)
      requires (V =/=K true) andBool (Ms =/=K .Match)
  rule matches(Exp, (P when V:Value-> E ; .Match)) => badmatch
      requires (V =/=K true)

  rule matches(Exp, P when _ -> E) => badmatch
      requires notBool (isMatching(Exp, P))

  rule matches(Exp, (P when _ -> E ; Ms)) => matches(Exp, Ms)
      requires (notBool (isMatching(Exp, P))) andBool (Ms =/=K .Match)

  syntax Exp ::= transformGS(GuardSeq) [function]
  rule transformGS(Gs:Exps; Gss:GuardSeq) => transformGs(Gs) orelse transformGS(Gss) requires Gss =/=K .GuardSeq
  rule transformGS(Gs:Exps; .GuardSeq)  => transformGs(Gs)
  rule transformGS(Gs:Exps)  => transformGs(Gs)

  syntax Exp ::= transformGs(Exps) [function]
  rule transformGs(G:Exp, Gs:Exps) => G andalso transformGs(Gs) requires Gs =/=K .Exps
  rule transformGs(G:Exp, .Exps) => G

  syntax Map ::= getMatching(Exp, Exp) [function]
  // initialize the map to empty
  rule getMatching(E, P) => getMatching1(E, P, .Map)

  syntax Map ::= getMatching1(Exp, Exp, Map) [function]
  // basic values
  rule getMatching1(E, P:BasicValue, M) => M
      requires isBasicMatch(E,P)
  rule getMatching1(E, P:BasicValue, M) => M[badmatch <- badmatch]
      requires notBool isBasicMatch(E,P)
  // allowing joker in patterns
  rule getMatching1(E, P:Joker, M) => M
  // variable matching: allowing non-linear patterns
  rule getMatching1(E, P:Variable, M) => M[P <- E]
      requires notBool (P in keys(M))
  rule getMatching1(E, P, M) => M
      requires (P in keys(M)) andBool (M[P] ==K E)
  rule getMatching1(E, P, M) => M[badmatch <- badmatch]
      requires (P in keys(M)) andBool (M[P] =/=K E)
  // tuples
  rule getMatching1({Xs}, {Ys}, M) => getMatchingList(Xs, Ys, M)
  // lists
  rule getMatching1([E1:Exps], [E2:Exps], M) => M
      requires (E1 ==K .Exps) andBool (E2 ==K .Exps)
  rule getMatching1([X:Value | Xs], [Y:Exp | Ys], M) => getMatching1(Xs, Ys, getMatching1(X, Y, M))

  rule getMatching1(_, _, M) => M[badmatch <- badmatch] [owise]

  syntax Map ::= getMatchingList(Exps, Exps, Map) [function]
  rule getMatchingList((.Exps), (.Exps), M) => M

  rule getMatchingList((X, Xs),(Y, Ys), M)  => getMatchingList(Xs,Ys, getMatching1(X,Y, M))
  rule getMatchingList(_, _, M) => M[badmatch <- badmatch] [owise]

  syntax Bool ::= isBasicMatch(Exp, BasicValue) [function]
  rule isBasicMatch(I1:Int, I2:Int) => I1 ==Int I2
  rule isBasicMatch(A1:Atom, A2:Atom) => A1 ==K A2
  rule isBasicMatch(_, _) => false [owise]

  syntax Bool ::= isMatching(Exp, Exp) [function]
  rule isMatching(E, P) => notBool (badmatch in (keys(getMatching(E, P))))

endmodule