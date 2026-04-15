// Bridge lemmas connecting FoldNDelta (normalized derivative fold) to Matches.
// These are needed to prove DFA correctness.

include "normalize.dfy"
include "walk.dfy"

/** Normalizing an expression preserves what strings it matches. */
lemma NormalizePreservesMatches<A(!new)>(e: Exp, s: seq<A>,
  normPlus: (Exp<A>, Exp<A>) -> Exp<A>)
  requires NormPlusSpec<A>(normPlus)
  ensures Matches(e, s) == Matches(Normalize(e, normPlus), s)
{
  NormalizeCorrect<A>(e, normPlus);
  BisimilarWalkEps(Denotational(Normalize(e, normPlus)), Denotational(e), s);
}

/** FoldNDelta agrees with FoldDelta on Eps, starting from the same expression. */
lemma FoldNDeltaEps<A(!new)>(e: Exp, s: seq<A>,
  normPlus: (Exp<A>, Exp<A>) -> Exp<A>)
  requires NormPlusSpec<A>(normPlus)
  ensures Eps(FoldDelta(e, s)) == Eps(FoldNDelta(e, s, normPlus))
  decreases |s|
{
  if |s| != 0 {
    var d := Delta(e, s[0]);
    var nd := Normalize(d, normPlus);
    NormalizePreservesMatches(d, s[1..], normPlus);
    MatchesEquivFoldDelta(d, s[1..]);
    MatchesEquivFoldDelta(nd, s[1..]);
    FoldNDeltaEps(nd, s[1..], normPlus);
  }
}

/** FoldNDelta(e, s + [a]) == NDelta(FoldNDelta(e, s), a). */
lemma FoldNDeltaAppend<A(!new)>(e: Exp, s: seq<A>, a: A,
  normPlus: (Exp<A>, Exp<A>) -> Exp<A>)
  ensures FoldNDelta(e, s + [a], normPlus) == NDelta(FoldNDelta(e, s, normPlus), a, normPlus)
  decreases |s|
{
  if |s| == 0 {
    assert s + [a] == [a];
  } else {
    assert (s + [a])[0] == s[0];
    assert (s + [a])[1..] == s[1..] + [a];
    FoldNDeltaAppend(NDelta(e, s[0], normPlus), s[1..], a, normPlus);
  }
}

/** Main bridge: Eps(FoldNDelta(Normalize(e), s)) == Matches(e, s). */
lemma FoldNDeltaCorrect<A(!new)>(e: Exp, s: seq<A>,
  normPlus: (Exp<A>, Exp<A>) -> Exp<A>)
  requires NormPlusSpec<A>(normPlus)
  ensures Eps(FoldNDelta(Normalize(e, normPlus), s, normPlus)) == Matches(e, s)
{
  NormalizePreservesMatches(e, s, normPlus);
  MatchesEquivFoldDelta(Normalize(e, normPlus), s);
  FoldNDeltaEps(Normalize(e, normPlus), s, normPlus);
}
