requires "erl-syntax.k"
requires "erl-configuration.k"
requires "erl-helpers.k"

module ERL-SUBSTITUTION

  imports ERL-SYNTAX
  imports ERL-CONFIGURATION
  imports ERL-HELPERS

  syntax Exp ::= subst(Exp, Map) [function]

  rule subst(A:Atom, _) => A
  rule subst(I:Int, _) => I

  rule subst(J:Joker, _) => J
  rule subst(V:Variable, Map) => V requires notBool (V in keys(Map))
  rule subst(V:Variable, Map) => {Map[V]}:>Exp requires (V in keys(Map))

  rule subst(not E, Map) => not subst(E, Map)

  // TODO: make it complete!
  //rule subst(E1 Op E2, Map) => subst(E1, Map) Op subst(E2, Map)
  rule subst(E1 + E2, Map) => subst(E1, Map) + subst(E2, Map)
  rule subst(E1 * E2, Map) => subst(E1, Map) * subst(E2, Map)
  rule subst(E1 rem E2, Map) => subst(E1, Map) rem subst(E2, Map)
  rule subst(E1 div E2, Map) => subst(E1, Map) div subst(E2, Map)
  rule subst(E1 - E2, Map) => subst(E1, Map) - subst(E2, Map)
  rule subst(E1 == E2, Map) => subst(E1, Map) == subst(E2, Map)
  rule subst(E1 /= E2, Map) => subst(E1, Map) /= subst(E2, Map)
  rule subst(E1 > E2, Map) => subst(E1, Map) > subst(E2, Map)
  rule subst(E1 < E2, Map) => subst(E1, Map) < subst(E2, Map)
  rule subst(E1 =< E2, Map) => subst(E1, Map) =< subst(E2, Map)
  rule subst(E1 >= E2, Map) => subst(E1, Map) >= subst(E2, Map)
  rule subst(E1 ++ E2, Map) => subst(E1, Map) ++ subst(E2, Map)
  rule subst(E1 -- E2, Map) => subst(E1, Map) -- subst(E2, Map)
  rule subst(E1 andalso E2, Map) => subst(E1, Map) andalso subst(E2, Map)
  rule subst(E1 orelse E2, Map) => subst(E1, Map) orelse subst(E2, Map)

  rule subst({ Es }, Map) => { substAll(Es, Map) }

  rule subst([Es:Exps], _) => [Es:Exps] requires Es ==K .Exps
  rule subst([Es | E], Map) => [ substAll(Es, Map) | subst(E, Map) ]

  rule subst(E:Exp(Es), Map) => subst(E, Map) ( substAll(Es, Map) )
  //rule subst((M:Exp):(E:Exp)(Es), Map) => subst(M, Map) : subst(E, Map) ( substAll(Es, Map) )
  rule subst(case E of M end, Map) => case subst(E, Map) of substMatch(M, Map) end
  rule subst(if IfBody end, Map) => if substIfBody(IfBody, Map) end
  rule subst(begin Es end, Map) => begin substAll(Es, Map) end
  rule subst(E1 = E2, Map) => subst(E1, Map) = subst(E2, Map)
  rule subst(fun Cls end, Map) => fun substCls(Cls, Map) end
  rule subst(fun N/A, Map) => fun (subst(N, Map)) / (subst(A, Map))

  rule subst([E || GFs], Map) => [subst(E, removeAll(Map, varsBoundedByGen(GFs))) || substGFs(GFs, Map)]

  syntax Set ::= varsBoundedByGen(GFs) [function]
  rule varsBoundedByGen((P:Exp <- _, GFs:GFs)) => fv(P) varsBoundedByGen(GFs)
  rule varsBoundedByGen((.GFs)) => (.Set)
  rule varsBoundedByGen((_, GFs:GFs)) => varsBoundedByGen(GFs) [owise]

  // shadowing!
  syntax GFs ::= substGFs(GFs, Map) [function]
  rule substGFs((P <- L, GFs), Map) =>  subst(P, removeAll(Map, fv(P))) <- subst(L, Map), substGFs(GFs, removeAll(Map, fv(P)))
  rule substGFs((.GFs), _) => (.GFs)
  rule substGFs((B, GFs), Map) => subst(B,Map), substGFs(GFs, Map) [owise]

  syntax Exps ::= substAll(Exps, Map) [function]
  rule substAll((E, Es), Map) => (subst(E, Map), substAll(Es, Map))
  rule substAll(EmptyList, _) => EmptyList [owise]

  syntax Match ::= substMatch(Match, Map) [function]
  rule substMatch((E1 -> E2; Ms), Map) => (subst(E1, Map) -> subst(E2, Map); substMatch(Ms, Map))
  rule substMatch(E1 -> E2, Map) => subst(E1, Map) -> subst(E2, Map)
  rule substMatch((E1 when G -> E2; Ms), Map) => (subst(E1, Map) when substGS(G, Map) -> subst(E2, Map); substMatch(Ms, Map))
  rule substMatch(E1 when G -> E2, Map) => (subst(E1, Map) when substGS(G, Map) -> subst(E2, Map))
  rule substMatch(EmptyMatch, _) => EmptyMatch [owise]

  syntax IfBody ::= substIfBody(IfBody, Map) [function]
  rule substIfBody((E1 -> E2; Ms), Map) => (substGS(E1, Map) -> subst(E2, Map); substIfBody(Ms, Map))
  rule substIfBody(E1 -> E2, Map) => substGS(E1, Map) -> subst(E2, Map)

  syntax Clauses ::= substCls(Clauses, Map) [function]
  rule substCls(((Args:Exps) -> E; Cls), Map) => (Args) -> substCl(Args, E, Map); substCls(Cls, Map)
  rule substCls((Args:Exps) -> E, Map) => (Args) -> substCl(Args, E, Map)
  rule substCls((Var (Args:Exps) -> E; Cls), Map) => Var (Args) -> substCl2(Args, Var, E, Map); substCls(Cls, Map)
  rule substCls(Var (Args:Exps) -> E, Map) => Var (Args) -> substCl2(Args, Var, E, Map)
  rule substCls(EmptyCls, _) => EmptyCls [owise]

  syntax GuardSeq ::= substGS(GuardSeq, Map) [function]
  rule substGS((G; Gs:GuardSeq), Map) => substAll(G, Map); substGS(Gs, Map)
  rule substGS(.GuardSeq, _) => .GuardSeq [owise]

  // shadowing!
  syntax Exp ::= substCl(Exps, Exp, Map) [function]
  rule substCl(Args, Exp, Map) => subst(Exp, removeAll(Map, fvs(Args)))
  syntax Exp ::= substCl2(Exps, Variable, Exp, Map) [function]
  rule substCl2(Args, Var, Exp, Map) => subst(Exp, removeAll(Map, fvs(Args) SetItem(Var)))

endmodule