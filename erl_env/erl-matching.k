requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-substitution.k"

module ERL-MATCHING

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-SUBSTITUTION

  // The resulted map of getMatching function contains this key
  // when the maching is unsuccesful.

  syntax Exp ::= matches(Value, Match)
  syntax Exp ::= matchesFun(Value, Match)
  syntax Exp ::= matchesAndRestore(Value, Match, Map)
  syntax Exp ::= matchesFunAndRestore(Value, Match, Map)
  syntax Exp ::= matchesFunAndRestoreAll(Value, Match, Map, Map, Map)

  //To avoid unnecessary environment restore
  rule <k> matchesAndRestore(Exp, Match, _) ~> restoreEnv(Env0) =>
           matches(Exp, Match) ~> restoreEnv(Env0) ...
       </k>
       
  rule <k> matchesAndRestore(Exp, Match, Env) ~> K:K =>
           matches(Exp, Match) ~> restoreEnv(Env) ~> K ...
       </k>
       requires notBool (isRestoreEnv(K))

  rule <k> matchesAndRestore(Exp, Match, Env)  =>
           matches(Exp, Match) ~> restoreEnv(Env)
       </k>

  //Fun

   rule <k> matchesFunAndRestore(Exp, Match, Env) =>
            matchesFun(Exp, Match) ~> restoreEnv(Env) ...
       </k>
  
  rule <k> matchesFunAndRestoreAll(Exp, Match, Env, FunVars, FunEnv) =>
           matchesFun(Exp, Match) ~> restoreAll(Env, FunVars, FunEnv) ...
       </k>

  // Without guards
  rule <k> matches(Exp, P -> _) => %badmatch ...</k>
       <env> Env </env>
      requires notBool (isMatching(Exp, P, Env))
  rule <k> matches(Exp, P -> Es) => begin Es end ...</k>
       <env> Env => updateMap(Env, getMatching(Exp, P, Env)) </env>
      requires isMatching(Exp, P, Env)    
  rule <k> matches(Exp, (P -> Es ; _)) => begin Es end ...</k>
       <env> Env => updateMap(Env,getMatching(Exp, P, Env)) </env>
      requires isMatching(Exp, P, Env)
  rule <k> matches(Exp, (P -> _ ; Ms)) => matches(Exp, Ms) ...</k>
       <env> Env </env>
      requires (notBool (isMatching(Exp, P, Env))) andBool (Ms =/=K .Match)

  // With guards
  // TODO: when we will have exceptions: exception means false

  rule <k> matches(Exp, (P when G:GuardSeq -> Es ; Ms)) =>
       transformGS(G) ~> matches(Exp, (P when ?_ -> Es ; Ms)) ~> restoreEnv(Env) ...</k>
       <env> Env =>  updateMap(Env,getMatching(Exp, P, Env)) </env>
      requires (notBool isValue(G)) andBool (isMatching(Exp, P, Env))
      // [heat]

  rule G:Value ~> matches(Exp, (P when _ -> Es ; Ms)) => matches(Exp, (P when G -> Es ; Ms))
      // [cool]

  rule matches(_, (_ when true -> Es ; _)) => begin Es end
  rule <k> matches(Exp, (_ when V:Value -> _ ; Ms)) ~> restoreEnv(Env) => matches(Exp, Ms) ... </k>
       <env> _ => Env </env>
      requires (V =/=K true) andBool (Ms =/=K .Match)
  rule matches(_, (_ when V:Value-> _ ; .Match)) => %badmatch
      requires (V =/=K true)

  rule <k> matches(Exp, P when _ -> _) => %badmatch </k>
       <env> Env </env>
      requires notBool (isMatching(Exp, P, Env))

  rule <k> matches(Exp, (P when _ -> _ ; Ms)) => matches(Exp, Ms) ...</k>
      <env> Env </env>
      requires (notBool (isMatching(Exp, P, Env))) andBool (Ms =/=K .Match)

  // Without guards - funs
  rule <k> matchesFun(Exp, P -> _) => %badmatch </k>
       <env> Env </env>
      requires notBool (isMatching(Exp, P, removeAll(Env, fvs(P))))
  rule <k> matchesFun(Exp, P -> Es) => begin Es end ...</k>
       <env> Env => updateMap(Env, getMatching(Exp, P, removeAll(Env, fvs(P)))) </env>
      requires isMatching(Exp, P,  removeAll(Env, fvs(P)))    
  rule <k> matchesFun(Exp, (P -> Es ; _)) => begin Es end ...</k>
       <env> Env => updateMap(Env,getMatching(Exp, P, removeAll(Env, fvs(P)))) </env>
      requires isMatching(Exp, P, removeAll(Env, fvs(P)))
  rule <k> matchesFun(Exp, (P -> _ ; Ms)) => matchesFun(Exp, Ms) ...</k>
       <env> Env </env>
      requires (notBool (isMatching(Exp, P, removeAll(Env, fvs(P))))) andBool (Ms =/=K .Match)

  //TODO: with guards fun

  syntax Exp ::= transformGS(GuardSeq) [function]
  rule transformGS(Gs:Exps; Gss:GuardSeq) => transformGs(Gs) orelse transformGS(Gss) requires Gss =/=K .GuardSeq
  rule transformGS(Gs:Exps; .GuardSeq)  => transformGs(Gs)
  rule transformGS(Gs:Exps)  => transformGs(Gs)

  syntax Exp ::= "%andalsofalse(" Exp "," Exp ")"    [strict(1)]
  rule %andalsofalse(true, B)   => B
  rule %andalsofalse(false, _)  => false
  rule %andalsofalse(V:Value, _) => false
    requires V =/=K true andBool V =/=K false

  syntax Exp ::= transformGs(Exps) [function]
  rule transformGs(G:Exp, Gs:Exps) => %andalsofalse(G, transformGs(Gs)) requires Gs =/=K .Exps
  rule transformGs(G:Exp, .Exps) => G

  syntax Map ::= getMatching(Exp, Exp, Map) [function]
  // initialize the temporary map to empty
  rule getMatching(E, P, Env) => getMatching1(E, P, Env, .Map)

  syntax Map ::= getMatching1(Exp, Exp, Map, Map) [function]

  // basic values
  rule getMatching1(E, P:BasicValue, Env, M) => updateMap(Env,M)
      requires isBasicMatch(E,P)
  rule getMatching1(E, P:BasicValue, Env, _) => Env[%badmatch <- %badmatch]
      requires notBool isBasicMatch(E,P) 
  
  // allowing joker in patterns
  rule getMatching1(_, _:Joker, Env, M) => updateMap(Env,M)

  // variable matching: allowing non-linear patterns 
  rule getMatching1(E, P:Variable, Env, M) => M[P <- E]
      requires notBool (P in keys(updateMap(Env,M)))
  rule getMatching1(E, P:Variable, Env, M) => updateMap(Env,M)
      requires (P in keys(M)) andBool (M[P] ==K E)
  rule getMatching1(E, P:Variable, Env, M) => updateMap(Env,M)
      requires (P in keys(Env)) andBool (Env[P] ==K E)

  // tuples
  rule getMatching1({Xs}:Value, {Ys}:Exp, Env, M) => getMatchingList(Xs, Ys, Env, M)
  // lists
  rule getMatching1([E1:Values]:Value, [E2:Exps]:Exp, Env, M) => updateMap(Env,M)
      requires (E1 ==K .Values) andBool (E2 ==K .Exps)
  rule getMatching1([X:Value | Xs]:Value, [Y:Exp | Ys]:Exp, Env, M) => getMatching1(Xs, Ys, Env, getMatching1(X, Y, Env, M))

  rule getMatching1(_, _, Env, _) => Env[%badmatch <- %badmatch] [owise]

  syntax Map ::= getMatchingList(Values, Exps, Map, Map) [function]
  rule getMatchingList((.Values), (.Exps), Env, M) => updateMap(Env,M)

  rule getMatchingList((X, Xs),(Y, Ys), Env, M)  =>
       getMatchingList(Xs,Ys, updateMap(Env,getMatching1(X,Y,Env,M)), getMatching1(X,Y,Env,M))
  rule getMatchingList(_, _, Env, _) => Env[%badmatch <- %badmatch] [owise]

  syntax Bool ::= isBasicMatch(Exp, BasicValue) [function]
  rule isBasicMatch(I1:Int, I2:Int) => I1 ==Int I2
  rule isBasicMatch(A1:Atom, A2:Atom) => A1 ==K A2
  rule isBasicMatch(_, _) => false [owise]

  syntax Bool ::= isMatching(Exp, Exp, Map) [function]
  rule isMatching(E, P, Env) => notBool (%badmatch in (keys(getMatching(E, P, Env))))

  // lemmas
  // rule %badmatch in (keys(getMatching1(E1, E2, _, _))) => E1 =/=K E2 [lemma] 
endmodule
