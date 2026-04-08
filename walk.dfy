// Walk: fold delta over a string, connecting Denotational and Operational
// to an imperative fold of Delta/Eps.

include "re.dfy"

/** Fold delta over a string on a formal language (ghost). */
ghost function Walk<A>(L: Languages.Lang, s: seq<A>): Languages.Lang
  decreases |s|
{
  if |s| == 0 then L else Walk(L.delta(s[0]), s[1..])
}

/** Fold Delta over a string on an expression (the derivative after reading s). */
function FoldDelta<A(==)>(e: Exp<A>, s: seq<A>): Exp<A>
  decreases |s|
{
  if |s| == 0 then e else FoldDelta(Delta(e, s[0]), s[1..])
}

/** The specification predicate: does expression e match string s? */
ghost predicate Matches<A(!new)>(e: Exp<A>, s: seq<A>) {
  Walk(Denotational(e), s).eps
}

/** Bisimilar languages stay bisimilar after walking the same string. */
lemma BisimilarWalk<A(!new)>(L1: Languages.Lang, L2: Languages.Lang, s: seq<A>)
  requires Bisimilar(L1, L2)
  ensures Bisimilar(Walk(L1, s), Walk(L2, s))
  decreases |s|
{
  if |s| != 0 {
    BisimilarWalk(L1.delta(s[0]), L2.delta(s[0]), s[1..]);
  }
}

/** Corollary: bisimilar languages agree on eps after walking the same string. */
lemma BisimilarWalkEps<A(!new)>(L1: Languages.Lang, L2: Languages.Lang, s: seq<A>)
  requires Bisimilar(L1, L2)
  ensures Walk(L1, s).eps == Walk(L2, s).eps
{
  BisimilarWalk(L1, L2, s);
}

/** Walking Operational(e) over s gives the same eps as Eps(FoldDelta(e, s)). */
lemma OperationalWalkEps<A(!new)>(e: Exp, s: seq<A>)
  ensures Walk(Operational(e), s).eps == Eps(FoldDelta(e, s))
  decreases |s|
{
  if |s| != 0 {
    assert Operational(e).delta(s[0]) == Operational(Delta(e, s[0]));
    OperationalWalkEps(Delta(e, s[0]), s[1..]);
  }
}

/** Main connection: Matches(e, s) iff Eps(FoldDelta(e, s)).
    This is the spec that the imperative matcher will use. */
lemma MatchesEquivFoldDelta<A(!new)>(e: Exp, s: seq<A>)
  ensures Matches(e, s) == Eps(FoldDelta(e, s))
{
  OperationalAndDenotationalAreBisimilar(e);
  BisimilarWalkEps(Operational(e), Denotational(e), s);
  OperationalWalkEps(e, s);
}
