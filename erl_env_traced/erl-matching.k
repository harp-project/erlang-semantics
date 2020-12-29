requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-substitution.k"

module ERL-MATCHING

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-SUBSTITUTION

  // The resulted map of getMatching function contains this key
  // when the maching is unsuccesful.
  // syntax Atom ::= "badmatch" [token]

  syntax Exp ::= matches(Value, Match)
  syntax Exp ::= matchesFun(Value, Match)
  syntax Exp ::= matchesAndRestore(Value, Match, Map)
  syntax Exp ::= matchesFunAndRestore(Value, Match, Map)
  syntax Exp ::= matchesFunAndRestoreAll(Value, Match, Map, Map, Map)

  //To avoid unnecessary environment restore
  rule <k> matchesAndRestore(Exp, Match, Env) ~> restoreEnv(Env0) =>
           matches(Exp, Match) ~> restoreEnv(Env0) ...
       </k>
       <trace> ... "matches_and_restore" |-> (V' => V' +Int 1) ... </trace>
       
  rule <k> matchesAndRestore(Exp, Match, Env) ~> K:K =>
           matches(Exp, Match) ~> restoreEnv(Env) ~> K ...
       </k>
       <trace> ... "matches_and_restore" |-> (V' => V' +Int 1) ... </trace>
    requires notBool (isRestoreEnv(K))

  rule <k> matchesAndRestore(Exp, Match, Env)  =>
           matches(Exp, Match) ~> restoreEnv(Env)
       </k>
       <trace> ... "matches_and_restore" |-> (V' => V' +Int 1) ... </trace>

  //Fun

   rule <k> matchesFunAndRestore(Exp, Match, Env) =>
            matchesFun(Exp, Match) ~> restoreEnv(Env) ...
       </k>
       <trace> ... "matches_fun_and_restore" |-> (V' => V' +Int 1) ... </trace>
  
  rule <k> matchesFunAndRestoreAll(Exp, Match, Env, FunVars, FunEnv) =>
           matchesFun(Exp, Match) ~> restoreAll(Env, FunVars, FunEnv) ...
       </k>
       <trace> ... "matches_fun_and_restore" |-> (V' => V' +Int 1) ... </trace>

  // Without guards
  rule <k> matches(Exp, P -> Es) => %badmatch ...</k> // ... needed?
       <env> Env </env>
       <trace> ... "matches" |-> (V' => V' +Int 1) ... </trace>
    requires notBool (isMatching(Exp, P, Env))
  rule <k> matches(Exp, P -> Es) => begin Es end ...</k>
       <env> Env => updateMap(Env, getMatching(Exp, P, Env)) </env>
       <trace> ... "matches" |-> (V' => V' +Int 1) ... </trace>
    requires isMatching(Exp, P, Env)    
  rule <k> matches(Exp, (P -> Es ; Ms)) => begin Es end ...</k>
       <env> Env => updateMap(Env,getMatching(Exp, P, Env)) </env>
        <trace> ... "matches" |-> (V' => V' +Int 1) ... </trace>
    requires isMatching(Exp, P, Env)
  rule <k> matches(Exp, (P -> Es ; Ms)) => matches(Exp, Ms) ...</k>
       <env> Env </env>
       <trace> ... "matches" |-> (V' => V' +Int 1) ... </trace>
    requires (notBool (isMatching(Exp, P, Env))) andBool (Ms =/=K .Match)

  // With guards
  // TODO: when we will have exceptions: exception means false

  rule <k> matches(Exp, (P when G:GuardSeq -> Es ; Ms)) =>
       transformGS(G) ~> matches(Exp, (P when HOLE -> Es ; Ms)) ~> restoreEnv(Env) ...</k>
       <env> Env =>  updateMap(Env,getMatching(Exp, P, Env)) </env>
    requires (notBool isValue(G)) andBool (isMatching(Exp, P, Env))
      // [heat]

  rule <k>G:Value ~> matches(Exp, (P when HOLE -> Es ; Ms)) => matches(Exp, (P when G -> Es ; Ms)) ...</k>
      // [cool]

  rule <k> matches(Exp, (P when true -> Es ; Ms)) => begin Es end ... </k>
       <trace> ... "matches_guard" |-> (V' => V' +Int 1) ... </trace>
  rule <k> matches(Exp, (P when V:Value -> Es ; Ms)) ~> restoreEnv(Env) => matches(Exp, Ms) ... </k>
       <env> Env0 => Env </env>
       <trace> ... "matches_guard" |-> (V' => V' +Int 1) ... </trace>
    requires (V =/=K true) andBool (Ms =/=K .Match)
  rule <k> matches(Exp, (P when V:Value-> Es ; .Match)) => %badmatch ...</k>
       <trace> ... "matches_guard" |-> (V' => V' +Int 1) ... </trace>
    requires (V =/=K true)

  rule <k> matches(Exp, P when _ -> Es) => %badmatch ... </k> // ... needed?
       <env> Env </env>
       <trace> ... "matches_guard" |-> (V' => V' +Int 1) ... </trace>
    requires notBool (isMatching(Exp, P, Env))

  rule <k> matches(Exp, (P when _ -> Es ; Ms)) => matches(Exp, Ms) ...</k>
      <env> Env </env>
      <trace> ... "matches_guard" |-> (V' => V' +Int 1) ... </trace>
    requires (notBool (isMatching(Exp, P, Env))) andBool (Ms =/=K .Match)

  // Without guards - funs
  rule <k> matchesFun(Exp, P -> Es) => %badmatch ... </k> // ... needed?
       <env> Env </env>
       <trace> ... "matches_fun" |-> (V' => V' +Int 1) ... </trace>
    requires notBool (isMatching(Exp, P, removeAll(Env, fvs(P))))
  rule <k> matchesFun(Exp, P -> Es) => begin Es end ...</k>
       <env> Env => updateMap(Env, getMatching(Exp, P, removeAll(Env, fvs(P)))) </env>
       <trace> ... "matches_fun" |-> (V' => V' +Int 1) ... </trace>
    requires isMatching(Exp, P,  removeAll(Env, fvs(P)))    
  rule <k> matchesFun(Exp, (P -> Es ; Ms)) => begin Es end ...</k>
       <env> Env => updateMap(Env,getMatching(Exp, P, removeAll(Env, fvs(P)))) </env>
       <trace> ... "matches_fun" |-> (V' => V' +Int 1) ... </trace>
    requires isMatching(Exp, P, removeAll(Env, fvs(P)))
  rule <k> matchesFun(Exp, (P -> Es ; Ms)) => matchesFun(Exp, Ms) ...</k>
       <env> Env </env>
      requires (notBool (isMatching(Exp, P, removeAll(Env, fvs(P))))) andBool (Ms =/=K .Match)

  //TODO: with guards fun

    /* NOTE: functions cannot be traced */
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
  rule getMatching1(E, P:BasicValue, Env, M) => Env[%badmatch <- %badmatch]
      requires notBool isBasicMatch(E,P) 
  // allowing joker in patterns
  rule getMatching1(E, P:Joker, Env, M) => updateMap(Env,M)

  // variable matching: allowing non-linear patterns 
  rule getMatching1(E, P:Variable, Env, M) => M[P <- E]
      requires notBool (P in keys(updateMap(Env,M)))
  rule getMatching1(E, P:Variable, Env, M) => updateMap(Env,M)
      requires (P in keys(M)) andBool (M[P] ==K E)
  rule getMatching1(E, P:Variable, Env, M) => updateMap(Env,M)
      requires (P in keys(Env)) andBool (Env[P] ==K E)

  // tuples
  rule getMatching1({Xs}, {Ys}, Env, M) => getMatchingList(Xs, Ys, Env, M)
  // lists
  rule getMatching1([E1:Exps], [E2:Exps], Env, M) => updateMap(Env,M)
      requires (E1 ==K .Exps) andBool (E2 ==K .Exps)
  rule getMatching1([X:Value | Xs], [Y:Exp | Ys], Env, M) => getMatching1(Xs, Ys, Env, getMatching1(X, Y, Env, M))

  rule getMatching1(_, _, Env, _) => Env[%badmatch <- %badmatch] [owise]

  syntax Map ::= getMatchingList(Exps, Exps, Map, Map) [function]
  rule getMatchingList((.Exps), (.Exps), Env, M) => updateMap(Env,M)

  rule getMatchingList((X, Xs),(Y, Ys), Env, M)  =>
       getMatchingList(Xs,Ys, updateMap(Env,getMatching1(X,Y,Env,M)), getMatching1(X,Y,Env,M))
  rule getMatchingList(_, _, Env, _) => Env[%badmatch <- %badmatch] [owise]

  syntax Bool ::= isBasicMatch(Exp, BasicValue) [function]
  rule isBasicMatch(I1:Int, I2:Int) => I1 ==Int I2
  rule isBasicMatch(A1:Atom, A2:Atom) => A1 ==K A2
  rule isBasicMatch(_, _) => false [owise]

  syntax Bool ::= isMatching(Exp, Exp, Map) [function]
  rule isMatching(E, P, Env) => notBool (%badmatch in (keys(getMatching(E, P, Env))))
/* ----------------------------------------------------------------------------- */
  // lemmas
  // rule badmatch in (keys(getMatching1(E1, E2, _, _))) => E1 =/=K E2 [lemma] 
endmodule
