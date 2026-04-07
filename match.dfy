// Verified on-the-fly regular expression matcher via Brzozowski derivatives.
// No backtracking: folds Delta over the input, checks Eps at the end.

include "walk.dfy"

/** Verified regex matcher. Returns true iff e matches s.
    Runs in O(|s|) derivative steps, no backtracking. */
method Match(e: Exp<char>, s: seq<char>) returns (accepts: bool)
  ensures accepts == Matches(e, s)
{
  MatchesEquivFoldDelta(e, s);
  // Now: Matches(e, s) == Eps(FoldDelta(e, s))

  var current := e;
  for i := 0 to |s|
    invariant current == FoldDelta(e, s[..i])
  {
    assert s[..i+1] == s[..i] + [s[i]];
    FoldDeltaAppend(e, s[..i], s[i]);
    current := Delta(current)(s[i]);
  }
  assert s[..|s|] == s;
  accepts := Eps(current);
}

/** FoldDelta(e, s + [a]) == FoldDelta(Delta(FoldDelta(e, s))(a), [])
    i.e., appending one character is the same as one more Delta step. */
lemma FoldDeltaAppend<A(!new)>(e: Exp<A>, s: seq<A>, a: A)
  ensures FoldDelta(e, s + [a]) == Delta(FoldDelta(e, s))(a)
  decreases |s|
{
  if |s| == 0 {
    assert s + [a] == [a];
  } else {
    assert (s + [a])[0] == s[0];
    assert (s + [a])[1..] == s[1..] + [a];
    FoldDeltaAppend(Delta(e)(s[0]), s[1..], a);
  }
}
