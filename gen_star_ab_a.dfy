// Auto-generated verified matcher -- do not edit by hand; regenerate via Codegen.
// Dafny proves: MatchSpecialized(s) == Eps(FoldNDelta(Normalize(TheExpr()), s)).
// == Matches(TheExpr(), s) then follows by the library lemma FoldNDeltaCorrect
// (bridge.dfy) -- apply it in an outer shell where you want the full regex spec.
include "compile.dfy"

function TheExpr(): Exp<char> { Comp(Star(Plus(Char('a'), Char('b'))), Char('a')) }

function S0(): Exp<char> { Comp(Star(Plus(Char('a'), Char('b'))), Char('a')) }
function S1(): Exp<char> { Plus(Comp(Star(Plus(Char('a'), Char('b'))), Char('a')), One) }

function Trans(state: nat, c: char): nat
  requires state < 2 && (c == 'a' || c == 'b')
  ensures Trans(state, c) < 2
{
  if state == 0 && c == 'a' then 1
  else if state == 0 && c == 'b' then 0
  else if state == 1 && c == 'a' then 1
  else if state == 1 && c == 'b' then 0
  else 0
}

predicate Accept(state: nat) requires state < 2 {
  state == 1
}

function FoldTrans(state: nat, s: seq<char>): nat
  requires state < 2
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures FoldTrans(state, s) < 2
  decreases |s|
{ if |s| == 0 then state else FoldTrans(Trans(state, s[0]), s[1..]) }

ghost function StateExpr(state: nat): Exp<char>
  requires state < 2
{
  if state == 0 then S0()
  else S1()
}

lemma TransCorrect(state: nat, c: char)
  requires state < 2 && (c == 'a' || c == 'b')
  ensures NDelta(StateExpr(state), c, NormPlus) == StateExpr(Trans(state, c))
{}

lemma AcceptCorrect(state: nat)
  requires state < 2
  ensures Accept(state) == Eps(StateExpr(state))
{}

lemma NormStart() ensures Normalize(TheExpr(), NormPlus) == S0() {}

lemma FoldTransCorrect(state: nat, s: seq<char>)
  requires state < 2
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures StateExpr(FoldTrans(state, s)) == FoldNDelta(StateExpr(state), s, NormPlus)
  decreases |s|
{
  if |s| != 0 {
    TransCorrect(state, s[0]);
    FoldTransCorrect(Trans(state, s[0]), s[1..]);
  }
}

lemma CorrectnessNDelta(s: seq<char>)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures Accept(FoldTrans(0, s)) == Eps(FoldNDelta(Normalize(TheExpr(), NormPlus), s, NormPlus))
{
  NormStart();
  FoldTransCorrect(0, s);
  AcceptCorrect(FoldTrans(0, s));
}

method RunDFA(s: seq<char>) returns (state: nat)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures state < 2
  ensures state == FoldTrans(0, s)
{
  state := 0;
  for i := 0 to |s|
    invariant 0 <= state < 2
    invariant FoldTrans(state, s[i..]) == FoldTrans(0, s)
  {
    assert s[i..] == [s[i]] + s[i+1..];
    state := Trans(state, s[i]);
  }
  assert s[|s|..] == [];
}

method MatchSpecialized(s: seq<char>) returns (accepts: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures accepts == Eps(FoldNDelta(Normalize(TheExpr(), NormPlus), s, NormPlus))
{
  var state := RunDFA(s);
  accepts := Accept(state);
  CorrectnessNDelta(s);
}
