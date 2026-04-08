// Bridge lemmas connecting FoldNDelta (normalized derivative fold) to Matches.
// These are needed to prove DFA correctness.

include "normalize.dfy"
include "walk.dfy"

/** Normalizing an expression preserves what strings it matches. */
lemma NormalizePreservesMatches<A(!new)>(e: Exp, s: seq<A>)
  ensures Matches(e, s) == Matches(Normalize(e), s)
{
  NormalizeCorrect<A>(e);
  BisimilarWalkEps(Denotational(Normalize(e)), Denotational(e), s);
}

/** FoldNDelta agrees with FoldDelta on Eps, starting from the same expression. */
lemma FoldNDeltaEps<A(!new)>(e: Exp, s: seq<A>)
  ensures Eps(FoldDelta(e, s)) == Eps(FoldNDelta(e, s))
  decreases |s|
{
  if |s| != 0 {
    var d := Delta(e, s[0]);
    var nd := Normalize(d);
    NormalizePreservesMatches(d, s[1..]);
    MatchesEquivFoldDelta(d, s[1..]);
    MatchesEquivFoldDelta(nd, s[1..]);
    FoldNDeltaEps(nd, s[1..]);
  }
}

/** Main bridge: Eps(FoldNDelta(Normalize(e), s)) == Matches(e, s). */
lemma FoldNDeltaCorrect<A(!new)>(e: Exp, s: seq<A>)
  ensures Eps(FoldNDelta(Normalize(e), s)) == Matches(e, s)
{
  NormalizePreservesMatches(e, s);
  MatchesEquivFoldDelta(Normalize(e), s);
  FoldNDeltaEps(Normalize(e), s);
}
