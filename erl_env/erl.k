/*!
\title{Erlang semantics}
\author{Judit H. Koszegi
        (\texttt{\koszegijudit@elte.hu})}
\organization{University of Kent, Eotvos Lorand University}
*/

//@ \section{Semantics}
requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-helpers.k"
requires "erl-forms.k"
requires "erl-bifs.k"
requires "erl-matching.k"

module ERL

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS
  imports ERL-FORMS
  imports ERL-BIFS
  imports ERL-MATCHING
  //imports ERL-SUBSTITUTION


//==============================================================================
// Semantics of expressions

// -----------------------------------------------------------------------------
// Desugaring macros

  // List to normal form

  rule [Es:Exps] => [Es | [.Exps]] requires Es =/=K .Exps      [structural, anywhere]

  rule [E:Exp,Es | T] => [E | [Es|T]] requires Es =/=K .Exps   [structural, anywhere]

// -----------------------------------------------------------------------------
// Varible lookup

  rule <k> Var:Variable => Value ...</k>
       <env> ... Var |-> Value ...</env>
       <funVars> FunVars  </funVars>
       requires notBool (Var in keys(FunVars))


  rule <k> Var:Variable => Value ...</k>
       <funVars> ... Var |-> Value ...</funVars>
       
// -----------------------------------------------------------------------------
// Arithmetic operators

  // syntax Atom ::= "%badarith" [token]

  rule I1 *   I2 => I1 *Int I2
  rule I1 div I2 => I1 /Int I2 requires I2 =/=Int 0
  rule I1 div I2 => %badarith requires I2 ==Int 0
  rule I1 rem I2 => I1 %Int I2 requires I2 =/=Int 0
  rule I1 rem I2 => %badarith requires I2 ==Int 0
  rule I1 +   I2 => I1 +Int I2
  rule I1 -   I2 => I1 -Int I2

// -----------------------------------------------------------------------------
// Comparison operators

  // TODO: add funs to comparison

  rule (E1:Int)    < (E2:Int)     => (E1 <Int E2)

  // converting Bool to String
  rule #tokenToString(true) => "true"   [anywhere]
  rule #tokenToString(false) => "false" [anywhere]

  rule (E1:Atom)   < (E2:Atom)    => #tokenToString(E1) <String #tokenToString(E2)

  rule (E1:Int)  < (E2:Atom)    => true
  rule (E1:Int)  < ({Es:Exps})  => true
  rule (E1:Int)  < [_]          => true
  rule (E1:Int)  < [_ | _]      => true
  rule (E1:Atom) < (E2:Int)     => false
  rule (E1:Atom) < {Vs}         => true
  rule (E1:Atom) < [_]          => true
  rule (E1:Atom) < [_ | _]      => true
  rule {Vs}      < (E2:Atom)    => false
  rule {Vs}      < (E2:Int)     => false
  rule [_]       < (E2:Atom)    => false
  rule [_|_]     < (E2:Atom)    => false
  rule [_]       < (E2:Int)     => false
  rule [_|_]     < (E2:Int)     => false
  rule {Vs}      < [_]          => true
  rule {Vs}      < [_|_]        => true
  rule [_]       < {Vs}         => false
  rule [_|_]     < {Vs}         => false

  rule {(.Values)}   < {(.Values)}       => false
  rule {(X:Value,Xs:Values)}  < {(Y:Value,Ys:Values)} => X < Y
       requires %count(Xs) ==Int 0 andBool %count(Ys) ==Int 0
       [structural]
  rule {(X:Value,Xs:Values)} < {(Y:Value,Ys:Values)} => (X < Y) orelse (X == Y andalso {Xs} < {Ys})
       requires %count(Xs) ==Int %count(Ys) andBool %count(Xs) >Int 0 andBool %count(Ys) >Int 0
       [structural]
  rule {(Xs:Values)} < {(Ys:Values)} => %count(Xs) <Int %count(Ys)
       requires %count(Xs) =/=Int %count(Ys)

  rule [.Exps]    < [V | Vs] => true
  rule [.Exps]    < [.Exps]  => false
  rule [V | Vs]   < [.Exps]  => false
  rule [V1 | Vs1] < [V2 | Vs2] => Vs1 < Vs2 requires eq(V1,V2) [structural]
  rule [V1 | Vs1] < [V2 | Vs2] => V1 < V2   requires notBool (eq(V1,V2)) [structural]

  rule (E1:Value) >= (E2:Value) => not (E1 < E2) [structural]
  rule (E1:Value) >  (E2:Value) => (E2 < E1)     [structural]
  rule (E1:Value) =< (E2:Value) => not (E2 < E1) [structural]

// -----------------------------------------------------------------------------
// Equality checks

  // TODO: add funs to equality checks

  rule V1 == V2 => eq(V1,V2)

  rule E1 /= E2 => not (E1 == E2) [structural]

  syntax Bool ::= eq(Value, Value) [function]

  rule eq(E1:Int,E2:Int) => E1 ==Int E2

  rule eq(E1:Atom,E2:Atom) => E1 ==K E2

  rule eq({(.Values)},{(.Values)}) => true
  rule eq({(X:Value, Xs:Values)},{(Y:Value, Ys:Values)}) => (eq(X,Y)) andBool (eq({Xs},{Ys}))

  rule eq([(.Values)],[(.Values)]) => true
  rule eq([(X:Value, .Values) | Xs], [(Y:Value, .Values) | Ys]) => (eq(X,Y)) andBool (eq(Xs,Ys))

  rule eq(_,_) => false [owise]

// -----------------------------------------------------------------------------
// Short-circuit logic operations

  // syntax Atom ::= "%badarg" [token]

  rule V1:Value and V2:Value => %badarg
    requires (V1 =/=K true andBool V1 =/=K false)
      orBool (V2 =/=K true andBool V2 =/=K false)
  rule V1:Value and V2:Value  => V1 andalso V2

  rule V1:Value or V2:Value => %badarg
    requires (V1 =/=K true andBool V1 =/=K false)
      orBool (V2 =/=K true andBool V2 =/=K false)
  rule V1:Value or V2:Value  => V1 orelse V2

  rule true  andalso B   => B
  rule false andalso _   => false
  rule V:Value andalso _ => %badarg requires V =/=K true andBool V =/=K false

  rule true  orelse  _   => true
  rule false orelse  B   => B
  rule V:Value orelse _  => %badarg requires V =/=K true andBool V =/=K false

  rule not true          => false
  rule not false         => true
  rule not V:Value       => %badarg requires V =/=K true andBool V =/=K false

// -----------------------------------------------------------------------------
// List operations

  rule [E1 | E1s] ++ E2 => [E1 | E1s ++ E2]
  rule [.Values] ++ E2 => E2
  // NOTE: _:Value restriction is needed to aviod wrong rewriting
  rule <k> _:Value ++ _ => %badarg ... </k> [owise]

  rule [.Values] -- [.Values] => [.Values]
  rule [.Values] -- [_ | _] => [.Values]
  rule [E1 | E1s] -- [E2 | Es2] => %removeElement(E2, [E1 | E1s]) -- Es2
  rule [E1 | E1s] -- [.Values] => [E1 | E1s]
  rule _:Value -- _:Value => %badarg  [owise]

  syntax Exp ::= "%removeElement(" Exp "," Exp ")"   [strict]
  rule %removeElement(E, [E1 | E1s]) => E1s requires eq(E,E1)
  rule %removeElement(E, [E1 | E1s]) => [E1 | %removeElement(E, E1s)] requires notBool (eq(E,E1))
  rule %removeElement(E, [.Exps]) => [.Exps]

// -----------------------------------------------------------------------------
// List comprehension

  rule [ E || (.GFs)] => [E]

  // TODO: fresh vars instead of "MyFun_111", "X_111" and "Xs_111"
  // rule [ E || P <- L, GFs] =>
  //     fun parseVar("MyFun_111")([(.Exps)]) ->
  //           [(.Exps)];
  //         parseVar("MyFun_111")([ parseVar("X_111"), (.Exps) | parseVar("Xs_111")], (.Exps)) ->
  //           case parseVar("X_111") of
  //             P         -> [E || GFs] ++ parseVar("MyFun_111")(parseVar("Xs_111"), (.Exps));
  //             (?X:Joker) -> parseVar("MyFun_111")(parseVar("Xs_111"), (.Exps))
  //           end
  //     end (L)

  // Another version (idea: https://www.haskell.org/onlinereport/exps.html#list-comprehensions)

  rule [ E || P <- L, GFs] =>
       %concatMap(fun (P) -> [E || GFs]; (?X:Joker) -> [(.Exps)] end, L)
       [structural]

  rule [ E || Bool, GFs] =>
      case Bool of
        true -> [E || GFs];
        (?X:Joker) -> [(.Exps)]
      end
      requires notBool (isGenerator(Bool))

  syntax Exp ::= "%concatMap(" Exp "," Exp ")"  [strict(2)]
  rule %concatMap(F, [(.Exps)]) => [(.Exps)]
  rule %concatMap(F, [X | Xs])  => F(X) ++ %concatMap(F, Xs)


// -----------------------------------------------------------------------------
// Function call

// FA call (local)

  rule <k>F:Atom(A:Values) =>
          matchesAndRestore({A}, getMatch(L), Env) ...</k>
       <env> Env => .Map </env>
       <currentMod> CurrentMod </currentMod>
       <mods> ...
         <mod>
           ...
           <modname> CurrentMod </modname>
           <fundefs>...  {F, %count(A)} |-> L:List ...</fundefs>
           ...
         </mod> ...
       </mods>
      requires notBool isBIF(F)

// FA call (imported)

  rule <k>F:Atom(A:Values) =>
          matchesAndRestore({A}, getMatch(L), Env) ~> restoreCurrentMod(CurrentMod) ...
       </k>
       <env> Env => .Map </env>
       <currentMod> CurrentMod => M </currentMod>
       <mods> ...
         <mod>
           ... 
           <modname> CurrentMod </modname>
           <imports> (S1:Set) SetItem({M, F, %count(A)}) </imports>
           ...
         </mod>
         <mod>
           ... 
           <modname> M </modname>
           <exports> (S2:Set) SetItem({F, %count(A)}) </exports>
           <fundefs>... {F, %count(A)} |-> L:List ...</fundefs>
           ...
         </mod> ...
       </mods>
      
// MFA call

  rule <k>(M:Atom):(F:Atom)(A:Values) =>
         matchesAndRestore({A}, getMatch(L), Env) ~> restoreCurrentMod(CurrentMod) ...
       </k>
       <env> Env => .Map </env>
       <currentMod> CurrentMod => M </currentMod>
       <mods> ...
         <mod>
           ... 
           <modname> Mod </modname>
           <exports> (S:Set) SetItem({F, %count(A)}) </exports>
           <fundefs>...  {F, %count(A)} |-> L:List ...</fundefs>
           ...
         </mod> ...
       </mods>

// Call to an anonymous function
  rule <k>(fun Cls:Clauses end)(Args) =>
          matchesFunAndRestore({Args}, getMatchFromFun(Cls), Env) ...</k>
       <env> Env </env>   
       requires (notBool (isNamedFun(fun Cls:Clauses end))) andBool (%count(Args) ==Int %clauseVars(Cls))
  
  rule <k>(fun Cls:Clauses end)(Args) => %badarity ...</k>
      <env> Env </env>
      requires (notBool (isNamedFun(fun Cls:Clauses end))) andBool (notBool %count(Args) ==Int %clauseVars(Cls))

// Call to an anonymous function with a variable as "name"
  rule <k>(fun Cls:Clauses end)(Args) =>
          matchesFunAndRestoreAll({Args}, getMatchFromFun(Cls), Env, FunVars, FunEnv) ...</k>
       <env> Env </env>
       <funVars> FunVars => updateMap(FunVars, getNewFunvar(fun Cls:Clauses end)) </funVars>
       <funEnv> FunEnv => FunEnv getFunvar(fun Cls:Clauses end) |-> Env</funEnv>
       requires (isNamedFun(fun Cls:Clauses end)) andBool (notBool (getFunvar(fun Cls:Clauses end) in keys(FunVars))) andBool (%count(Args) ==Int %clauseVars(Cls))

// Recursive call to a "named" anonymous function
  rule <k> (fun Cls:Clauses end)(Args) =>
           matchesFunAndRestore({Args}, getMatchFromFun(Cls), Env) ... </k>
       <env> Env => FunEnv </env>
       <funVars> FunVars </funVars>
       <funEnv> ... getFunvar(fun Cls:Clauses end) |-> FunEnv ... </funEnv>
       requires (isNamedFun(fun Cls:Clauses end)) andBool (getFunvar(fun Cls:Clauses end) in keys(FunVars)) andBool (%count(Args) ==Int %clauseVars(Cls))

// Call to an implicit fun
  rule fun Name:Atom/Arity:Int(Args) =>
       fun(genArgs(Arity)) -> Name(genArgs(Arity)) end(Args) [structural]

// Call exceptions
  rule <k>F:Atom(A:Values) => %badarity ...</k>
       <env> Env => .Map </env>
       <currentMod> CurrentMod </currentMod>
       <funnames> (S:Set) SetItem(F) </funnames>
       <mods> ...
         <mod>
           ...
           <modname> CurrentMod </modname>
           ...
         </mod> ...
       </mods>
      requires notBool isBIF(F)   [owise]

  rule <k>F:Value(A:Values) => %badfun ...</k>
       <env> Env => .Map </env>
       <currentMod> CurrentMod </currentMod>
       
       <mods> ...
         <mod>
           ...
           <modname> CurrentMod </modname>
           ...
         </mod> ...
       </mods>
      requires notBool isAtom(F)  [owise]

  rule <k> F:Atom(Vs:Values) => %undef ... </k> 
    requires (notBool isBIF(F)) [owise]

// -----------------------------------------------------------------------------
// If expression

  rule if Gs -> E end => case true of true when Gs -> E end
     [structural]

  rule if Gs -> E; GCl end => case true of true when Gs -> E; true -> if GCl end end
     [structural]

// -----------------------------------------------------------------------------
// Case expression

  rule <k> case E:Value of M:Match end => matchesAndRestore(E,M,Env) ... </k>
       <env> Env </env>

// -----------------------------------------------------------------------------
// Begin - end

  //So far, we are only able to write expression sequence in a begin-end block

  // rule E, .Exps => E // TODO / BEWARE / CAUTION / this may be too permissive

  rule begin E, Es end => E
      requires Es ==K .Exps

  rule begin P = E, Es end => case E of P -> begin Es end end
      requires Es =/=K .Exps

  rule begin E , Es end => (case E of (?X:Joker) -> begin Es end end)
      requires notBool (isMatchExp(E)) andBool (Es =/=K .Exps)

// -----------------------------------------------------------------------------
// Match expression

  rule P = E => E

// =============================================================================
// Local helper functions


  // Rebuild the sequence of matches (separated by cemicolons) from the list
  // stored in the function definition environment .
  syntax Match ::= getMatch(List) [function]
  rule getMatch(ListItem(X:Match0)) => X
  rule getMatch(ListItem(X:Match0) L) => X ; (getMatch(L)) requires L =/=K .List

  syntax Match ::= "head_mismatch" [token] // TODO: replace it with an exception
  syntax Match ::= getMatchFromFun(Clauses) [function]
  rule getMatchFromFun((Es) -> E) => {Es} -> E
  rule getMatchFromFun((Es) -> E; Cls:Clauses) => {Es} -> E ;  getMatchFromFun(Cls)
      requires Cls =/=K .Clauses
  rule getMatchFromFun(Var:Variable (Es) -> E) => {Es} -> E
  rule getMatchFromFun(Var:Variable (Es) -> E; Cls:Clauses) => {Es} -> E ; getMatchFromFunWithVar(Cls, Var)
      requires Cls =/=K .Clauses

  syntax Match ::= getMatchFromFunWithVar(Clauses, Variable) [function]
  rule getMatchFromFunWithVar(Var (Es) -> E, Var) => {Es} -> E
  rule getMatchFromFunWithVar(Var (Es) -> E; Cls:Clauses, Var) => {Es} -> E ; getMatchFromFunWithVar(Cls, Var)
      requires Cls =/=K .Clauses
  rule getMatchFromFunWithVar(_, _) => head_mismatch [owise]

  syntax Map ::= getNewFunvar(Exp) [function]
  rule getNewFunvar(fun Var (Es) -> E end) => Var |-> (fun Var (Es) -> E end)
  rule getNewFunvar(fun Var (Es) -> E; Cls:Clauses end) => Var |->  (fun Var (Es) -> E; Cls:Clauses end)
  rule getNewFunvar(_) => .Map [owise]

  syntax Variable ::= getFunvar(Exp) [function]
  rule getFunvar(fun Var (Es) -> E end) => Var
  rule getFunvar(fun Var (Es) -> E; Cls:Clauses end) => Var
  rule getFunvar(_) => . [owise]

  syntax Bool ::= isNamedFun(Exp) [function]
  rule isNamedFun(Fun) => getNewFunvar(Fun) =/=K .Map

  // Need for restrore module environment after an MFA call
  syntax Exp ::= "restoreCurrentMod" "(" Atom ")"
  rule <k> Val:KResult ~> restoreCurrentMod(Mod) => Val ...</k>
       <currentMod> CorrentMod => Mod </currentMod>

  syntax Exps ::= genArgs(Int) [function]
  rule genArgs(0) => .Exps
  rule genArgs(N) => (#parseToken("Variable", "Arg" +String Int2String(N))), genArgs(N -Int 1)
      requires N >Int 0

  syntax Int ::= "%clauseVars(" Clauses ")"  [function]
  rule %clauseVars((Es) -> _; _) => %count(Es)
  rule %clauseVars(_(Es) -> _; _) => %count(Es) 

endmodule
