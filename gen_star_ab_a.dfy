// Auto-generated verified matcher for (a|b)*a
// Self-certifying: Dafny proves accepts == Matches(TheExpr(), s)

include "compile.dfy"

function TheExpr(): Exp<char> { Comp(Star(Plus(Char('a'), Char('b'))), Char('a')) }

// DFA states as normalized derivative expressions
function S0(): Exp<char> { Comp(Star(Plus(Char('a'), Char('b'))), Char('a')) }
function S1(): Exp<char> { Plus(Comp(Star(Plus(Char('a'), Char('b'))), Char('a')), One) }

// Inlined DFA as pure functions on nats (no maps, no Exp at runtime)
function Trans(state: nat, c: char): nat
  requires state < 2 && (c == 'a' || c == 'b')
  ensures Trans(state, c) < 2
{
  if state == 0 && c == 'a' then 1
  else if state == 1 && c == 'a' then 1
  else 0
}

predicate Accept(state: nat) requires state < 2 { state == 1 }

// Fold transitions over a string
function FoldTrans(state: nat, s: seq<char>): nat
  requires state < 2
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures FoldTrans(state, s) < 2
  decreases |s|
{
  if |s| == 0 then state else FoldTrans(Trans(state, s[0]), s[1..])
}

// Ghost: map state ids to derivative expressions
ghost function StateExpr(state: nat): Exp<char>
  requires state < 2
{ if state == 0 then S0() else S1() }

// Verified: transitions match normalized derivatives
lemma TransCorrect(state: nat, c: char)
  requires state < 2 && (c == 'a' || c == 'b')
  ensures NDelta(StateExpr(state), c) == StateExpr(Trans(state, c))
{}

lemma AcceptCorrect(state: nat)
  requires state < 2
  ensures Accept(state) == Eps(StateExpr(state))
{}

lemma NormStart() ensures Normalize(TheExpr()) == S0() {}

// Key lemma: FoldTrans tracks FoldNDelta
lemma FoldTransCorrect(state: nat, s: seq<char>)
  requires state < 2
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures StateExpr(FoldTrans(state, s)) == FoldNDelta(StateExpr(state), s)
  decreases |s|
{
  if |s| != 0 {
    TransCorrect(state, s[0]);
    FoldTransCorrect(Trans(state, s[0]), s[1..]);
  }
}

// Accept(FoldTrans(0, s)) == Eps(FoldNDelta(Normalize(TheExpr()), s))
lemma CorrectnessNDelta(s: seq<char>)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures Accept(FoldTrans(0, s)) == Eps(FoldNDelta(Normalize(TheExpr()), s))
{
  NormStart();
  FoldTransCorrect(0, s);
  AcceptCorrect(FoldTrans(0, s));
}


// FoldTrans append lemma
lemma FoldTransAppend(state: nat, s: seq<char>, c: char)
  requires state < 2
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  requires c == 'a' || c == 'b'
  ensures FoldTrans(state, s + [c]) == Trans(FoldTrans(state, s), c)
  decreases |s|
{
  if |s| != 0 {
    assert (s + [c])[0] == s[0];
    assert (s + [c])[1..] == s[1..] + [c];
    FoldTransAppend(Trans(state, s[0]), s[1..], c);
  }
}

// Run the inlined DFA
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

// The specialized matcher
method MatchSpecialized(s: seq<char>) returns (accepts: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  ensures accepts == Eps(FoldNDelta(Normalize(TheExpr()), s))
{
  var state := RunDFA(s);
  accepts := state == 1;
  CorrectnessNDelta(s);
}

method Main() {
  var r1 := MatchSpecialized("a");     print "(a|b)*a  \"a\"    => ", r1, "\n";
  var r2 := MatchSpecialized("ba");    print "(a|b)*a  \"ba\"   => ", r2, "\n";
  var r3 := MatchSpecialized("ab");    print "(a|b)*a  \"ab\"   => ", r3, "\n";
  var r4 := MatchSpecialized("abba");  print "(a|b)*a  \"abba\" => ", r4, "\n";
  var r5 := MatchSpecialized("");      print "(a|b)*a  \"\"     => ", r5, "\n";
}
