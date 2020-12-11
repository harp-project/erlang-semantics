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
requires "erl-substitution.k"

module ERL

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS
  imports ERL-FORMS
  imports ERL-BIFS
  imports ERL-MATCHING
  imports ERL-SUBSTITUTION


//==============================================================================
// Semantics of expressions

// -----------------------------------------------------------------------------
// Desugaring macros

  // List to normal form

  rule [Es:Exps] => [Es | [.Exps]] requires Es =/=K .Exps      [macro]

  rule [E:Exp,Es | T] => [E | [Es|T]] requires Es =/=K .Exps   [macro]

// -----------------------------------------------------------------------------
// Arithmetic operators

  rule I1 *   I2 => I1 *Int I2
  rule I1 div I2 => I1 /Int I2 requires I2 =/=Int 0
  rule I1 rem I2 => I1 %Int I2 requires I2 =/=Int 0
  rule I1 +   I2 => I1 +Int I2
  rule I1 -   I2 => I1 -Int I2

// -----------------------------------------------------------------------------
// Comparison operators

  // TODO: add funs to comparison

  rule (E1:Int)    < (E2:Int)     => (E1 <Int E2)

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
       requires count(Xs) ==Int 0 andBool count(Ys) ==Int 0
       [structural]
  rule {(X:Value,Xs:Values)} < {(Y:Value,Ys:Values)} => (X < Y) orelse (X == Y andalso {Xs} < {Ys})
       requires count(Xs) ==Int count(Ys) andBool count(Xs) >Int 0 andBool count(Ys) >Int 0
       [structural]
  rule {(X:Value,Xs:Values)} < {(Y:Value,Ys:Values)} => count(Xs) <Int count(Ys)
       requires count(Xs) =/=Int count(Ys)

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

  syntax Atom ::= "badarg" [token]

  rule true  andalso B   => B
  rule false andalso _   => false
  rule V:Value andalso _ => badarg requires V =/=K true andBool V =/=K false

  rule true  orelse  _   => true
  rule false orelse  B   => B
  rule V:Value orelse _  => badarg requires V =/=K true andBool V =/=K false

  rule not true          => false
  rule not false         => true
  rule not V:Value       => badarg requires V =/=K true andBool V =/=K false

// -----------------------------------------------------------------------------
// List operations

  rule [E1 | E1s] ++ E2 => [E1 | E1s ++ E2]
  rule [.Exps] ++ E2 => E2

  rule [.Exps] -- [.Exps] => [.Exps]
  rule [.Exps] -- [_ | _] => [.Exps]
  rule [E1 | E1s] -- [E2 | Es2] => removeElement(E2, [E1 | E1s]) -- Es2
  rule [E1 | E1s] -- [.Exps] => [E1 | E1s]

  syntax Exp ::= removeElement(Exp, Exp)
  rule removeElement(E, [E1 | E1s]) => E1s requires eq(E,E1)
  rule removeElement(E, [E1 | E1s]) => [E1 | removeElement(E, E1s)] requires notBool (eq(E,E1))
  rule removeElement(E, [.Exps]) => [.Exps]

// -----------------------------------------------------------------------------
// List comprehension

  rule [ E || (.GFs)] => [E]

  // TODO: fresh vars instead of "MyFun_111", "X_111" and "Xs_111"
  rule [ E || P <- L, GFs] =>
      fun parseVar("MyFun_111")([(.Exps)]) ->
            [(.Exps)];
          parseVar("MyFun_111")([ parseVar("X_111"), (.Exps) | parseVar("Xs_111")], (.Exps)) ->
            case parseVar("X_111") of
              P         -> [E || GFs] ++ parseVar("MyFun_111")(parseVar("Xs_111"), (.Exps));
              (?X:Joker) -> parseVar("MyFun_111")(parseVar("Xs_111"), (.Exps))
            end
      end (L)

  rule [ E || Bool, GFs] =>
      case Bool of
        true -> [E || GFs];
        (?X:Joker) -> [(.Exps)]
      end

  // Another version (idea: https://www.haskell.org/onlinereport/exps.html#list-comprehensions)

  // rule [ E || P <- L, GFs] =>
  //      begin
  //        #parseToken("Variable", "MyFun") = fun (P) -> [E || GFs];(?X:Joker) -> [(.Exps)] end,
  //        concatMap(#parseToken("Variable", "MyFun"), L)
  //      end                     [structural]

  // syntax Exp ::= concatMap(Exp, Exp)   [function]
  // rule concatMap(F, [(.Exps)]) => [(.Exps)]
  // rule concatMap(F, [X | Xs]) => F(X) ++ concatMap(F, Xs)

// -----------------------------------------------------------------------------
// Function call

// FA call (local)

  rule <k>F:Atom(A) =>
          case {A} of (getMatch(L)) end ...</k>
       <currentmod> CurrentMod </currentmod>
       <mods> ...
         <mod>
           ...
           <modName> CurrentMod </modName>
           <defs>...  {F, count(A)} |-> L:List ...</defs>
           ...
         </mod> ...
       </mods>
      requires notBool isBIF(F)

// FA call (imported)

  rule <k>F:Atom(A) =>
          case {A} of (getMatch(L)) end ~> restoreCurrentMod(CurrentMod) ...
       </k>
       <currentmod> CurrentMod => M </currentmod>
       <mods> ...
         <mod>
           ... 
           <modName> CurrentMod </modName>
           <imports> (S1:Set) SetItem({M, F, count(A)}) </imports>
           ...
         </mod>
         <mod>
           ... 
           <modName> M </modName>
           <exports> (S2:Set) SetItem({F, count(A)}) </exports>
           <defs>... {F, count(A)} |-> L:List ...</defs>
           ...
         </mod> ...
       </mods>
      
// MFA call

  rule <k>(M:Atom):(F:Atom)(A) =>
          case {A} of (getMatch(L)) end ~> restoreCurrentMod(CurrentMod) ...
       </k>
       <currentmod> CurrentMod => M </currentmod>
       <mods> ...
         <mod>
           ... 
           <modName> Mod </modName>
           <exports> (S:Set) SetItem({F, count(A)}) </exports>
           <defs>...  {F, count(A)} |-> L:List ...</defs>
           ...
         </mod> ...
       </mods>

// Call to an Anonymous function
  rule <k>(fun Cls:Clauses end)(Args) =>
          case {Args} of getMatchFromFun(Cls) end ~> restoreFunvars(Funvars) ...</k>
       <funvars> Funvars => (Funvars -Map getNewFunvar(fun Cls:Clauses end)) getNewFunvar(fun Cls:Clauses end) </funvars>
      // -Map needed because Map concatenation cannnot handle maps with common keys

  // Varible referencig to an anonymous function (recursive fun)
  rule <k> V:Variable => Fun ...</k>
       <funvars> ... V |-> Fun ...</funvars>

  rule fun Name:Atom/Arity:Int(Args) =>
       fun(genArgs(Arity)) -> Name(genArgs(Arity)) end(Args) [structural]
  
  syntax Exps ::= genArgs(Int) [function]
  rule genArgs(0) => .Exps
  rule genArgs(N) => (#parseToken("Variable", "Arg" +String Int2String(N))), genArgs(N -Int 1)
    requires N >Int 0

// -----------------------------------------------------------------------------
// If expression

  rule if Gs -> E end => case true of true when Gs -> E end
      [structural]

  rule if Gs -> E; GCl end => case true of true when Gs -> E; true -> if GCl end end
      [structural]

// -----------------------------------------------------------------------------
// Case expression

  rule case E:Value of M:Match end => matches(E,M)

// -----------------------------------------------------------------------------
// Begin - end

  //So far, we are only able to write expression sequence in a begin-end block

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

  // Need for evaluating anonymous functions with named clauses
  syntax Exp ::= "restoreFunvars" "("Map")"
  rule <k> Val:KResult ~> restoreFunvars(Orig) => Val ...</k>
       <funvars> Funvars => Orig </funvars>

  // Need for restrore module environment after an MFA call
  syntax Exp ::= "restoreCurrentMod" "(" Atom ")"
  rule <k> Val:KResult ~> restoreCurrentMod(Mod) => Val ...</k>
       <currentmod> CorrentMod => Mod </currentmod>


endmodule
