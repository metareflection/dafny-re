// DFA compilation via BFS over normalized Brzozowski derivatives.
// Proven correct: DFAAccepts(dfa, s) <==> Matches(e, s).

include "bridge.dfy"

/** A compiled DFA: states 0..nStates-1, transition table, accepting set. */
datatype DFA = DFA(
  nStates: nat,
  start: nat,
  accepting: set<nat>,
  trans: map<(nat, char), nat>,
  ghost exprs: seq<Exp<char>>  // ghost: state id -> normalized derivative
)

/** Whether a DFA is well-formed for a given alphabet. */
ghost predicate WellFormedDFA(dfa: DFA, alphabet: set<char>) {
  && dfa.nStates > 0
  && dfa.nStates == |dfa.exprs|
  && dfa.start < dfa.nStates
  && (forall s :: s in dfa.accepting ==> s < dfa.nStates)
  && (forall st, c :: 0 <= st < dfa.nStates && c in alphabet ==>
       (st, c) in dfa.trans && dfa.trans[(st, c)] < dfa.nStates)
}

/** The DFA faithfully represents the derivative structure. */
ghost predicate DFACorrect(dfa: DFA, e: Exp<char>, alphabet: set<char>) {
  && WellFormedDFA(dfa, alphabet)
  && dfa.exprs[dfa.start] == NormalizeC(e)
  && (forall st, c :: 0 <= st < dfa.nStates && c in alphabet ==>
       dfa.exprs[dfa.trans[(st, c)]] == NDeltaC(dfa.exprs[st], c))
  && (forall st :: 0 <= st < dfa.nStates ==>
       (st in dfa.accepting <==> Eps(dfa.exprs[st])))
}

/** Helper: convert stateOf-based correctness to exprs-based correctness. */
ghost predicate DFACorrectViaMap(
  exprs: seq<Exp<char>>, stateOf: map<Exp<char>, nat>,
  trans: map<(nat, char), nat>, e: Exp<char>, alphabet: set<char>,
  accepting: set<nat>)
{
  && |exprs| > 0
  && (forall i :: 0 <= i < |exprs| ==> exprs[i] in stateOf && stateOf[exprs[i]] == i)
  && (forall expr :: expr in stateOf ==> stateOf[expr] < |exprs|)
  && (forall expr :: expr in stateOf ==> exprs[stateOf[expr]] == expr)
  && exprs[0] == NormalizeC(e)
  && (forall i, c :: 0 <= i < |exprs| && c in alphabet ==>
       (i, c) in trans && NDeltaC(exprs[i], c) in stateOf &&
       trans[(i, c)] == stateOf[NDeltaC(exprs[i], c)])
  && (forall st :: 0 <= st < |exprs| ==> (st in accepting <==> Eps(exprs[st])))
  && (forall st :: st in accepting ==> st < |exprs|)
  && (forall st, c :: 0 <= st < |exprs| && c in alphabet ==>
       (st, c) in trans && trans[(st, c)] < |exprs|)
}

lemma DFACorrectFromMap(
  exprs: seq<Exp<char>>, stateOf: map<Exp<char>, nat>,
  trans: map<(nat, char), nat>, e: Exp<char>, alphabet: set<char>,
  accepting: set<nat>)
  requires DFACorrectViaMap(exprs, stateOf, trans, e, alphabet, accepting)
  ensures DFACorrect(
    DFA(|exprs|, 0, accepting, trans, exprs), e, alphabet)
{
  var dfa := DFA(|exprs|, 0, accepting, trans, exprs);
  forall st, c | 0 <= st < dfa.nStates && c in alphabet
    ensures dfa.exprs[dfa.trans[(st, c)]] == NDeltaC(dfa.exprs[st], c)
  {
    var tid := trans[(st, c)];
    assert tid == stateOf[NDeltaC(exprs[st], c)];
    assert exprs[tid] == NDeltaC(exprs[st], c);
  }
}

/** DFA run: follow transitions from a given state. */
function DFARun(dfa: DFA, s: seq<char>, state: nat, alphabet: set<char>): bool
  requires WellFormedDFA(dfa, alphabet)
  requires state < dfa.nStates
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
  decreases |s|
{
  if |s| == 0 then state in dfa.accepting
  else DFARun(dfa, s[1..], dfa.trans[(state, s[0])], alphabet)
}

/** DFA acceptance from the start state. */
predicate DFAAccepts(dfa: DFA, s: seq<char>, alphabet: set<char>)
  requires WellFormedDFA(dfa, alphabet)
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
{
  DFARun(dfa, s, dfa.start, alphabet)
}

/** A correct DFA accepts exactly the language of the original expression. */
lemma DFARunCorrect(dfa: DFA, e: Exp<char>, s: seq<char>,
  state: nat, alphabet: set<char>)
  requires DFACorrect(dfa, e, alphabet)
  requires state < dfa.nStates
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
  ensures DFARun(dfa, s, state, alphabet) == Eps(FoldNDeltaC(dfa.exprs[state], s))
  decreases |s|
{
  if |s| != 0 {
    var next := dfa.trans[(state, s[0])];
    assert dfa.exprs[next] == NDeltaC(dfa.exprs[state], s[0]);
    DFARunCorrect(dfa, e, s[1..], next, alphabet);
  }
}

lemma DFAAcceptsCorrect(dfa: DFA, e: Exp<char>, s: seq<char>,
  alphabet: set<char>)
  requires DFACorrect(dfa, e, alphabet)
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
  ensures DFAAccepts(dfa, s, alphabet) == Matches(e, s)
{
  DFARunCorrect(dfa, e, s, dfa.start, alphabet);
  assert dfa.exprs[dfa.start] == NormalizeC(e);
  NormalizeCIsNormalize(e);
  NormPlusCharSatisfiesSpec();
  FoldNDeltaCIsFoldNDelta(NormalizeC(e), s);
  FoldNDeltaCorrect(e, s, NormPlusChar);
}

/** Imperative DFA matcher. */
method {:isolate_assertions} DFAMatch(dfa: DFA, e: Exp<char>, s: seq<char>, alphabet: set<char>)
    returns (accepts: bool)
  requires DFACorrect(dfa, e, alphabet)
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
  ensures accepts == Matches(e, s)
{
  DFAAcceptsCorrect(dfa, e, s, alphabet);
  var state := dfa.start;
  for i := 0 to |s|
    invariant 0 <= state < dfa.nStates
    invariant state == dfa.start || true  // just for the type
    invariant DFARun(dfa, s[i..], state, alphabet) == DFAAccepts(dfa, s, alphabet)
  {
    assert s[i..] == [s[i]] + s[i+1..];
    state := dfa.trans[(state, s[i])];
  }
  assert s[|s|..] == [];
  accepts := state in dfa.accepting;
}

/** Convert a set to a sequence. */
method SetToSeq(s: set<char>) returns (sq: seq<char>)
  ensures |sq| == |s|
  ensures forall c :: c in s <==> c in sq
  ensures forall i, j :: 0 <= i < j < |sq| ==> sq[i] != sq[j]
{
  sq := [];
  var remaining := s;
  while |remaining| > 0
    invariant remaining <= s
    invariant |sq| + |remaining| == |s|
    invariant forall c :: c in sq <==> c in s && c !in remaining
    invariant forall i, j :: 0 <= i < j < |sq| ==> sq[i] != sq[j]
  {
    var c :| c in remaining;
    sq := sq + [c];
    remaining := remaining - {c};
  }
}

/** Compile a regex over a finite alphabet into a correct DFA.
    Uses decreases * as finiteness of derivative classes is not proven. */
method Compile(e: Exp<char>, alphabet: set<char>) returns (dfa: DFA)
  requires |alphabet| > 0
  decreases *
  ensures DFACorrect(dfa, e, alphabet)
{
  var alphaSeq := SetToSeq(alphabet);
  var startExpr := NormalizeC(e);

  var states: seq<Exp<char>> := [startExpr];
  var stateOf: map<Exp<char>, nat> := map[startExpr := 0];
  var trans: map<(nat, char), nat> := map[];
  var expanded: seq<bool> := [false];

  var done := false;
  while !done
    invariant |states| == |stateOf| == |expanded|
    invariant |states| > 0
    invariant states[0] == startExpr
    invariant forall i :: 0 <= i < |states| ==>
      states[i] in stateOf && stateOf[states[i]] == i
    invariant forall expr :: expr in stateOf ==> stateOf[expr] < |states|
    invariant forall expr :: expr in stateOf ==> states[stateOf[expr]] == expr
    invariant forall p :: p in trans ==> p.0 < |states| && trans[p] < |states|
    // Transition correctness: expanded states have all transitions, each correct
    invariant forall i, c :: 0 <= i < |states| && expanded[i] && c in alphabet ==>
      (i, c) in trans && NDeltaC(states[i], c) in stateOf &&
      trans[(i, c)] == stateOf[NDeltaC(states[i], c)]
    invariant done ==> forall i :: 0 <= i < |expanded| ==> expanded[i]
    decreases *
  {
    var found := -1;
    for i := 0 to |expanded|
      invariant forall j :: 0 <= j < i ==> expanded[j]
      invariant found == -1
    {
      if !expanded[i] { found := i; break; }
    }

    if found == -1 {
      done := true;
    } else {
      var sid := found;
      var expr := states[sid];

      var chars := SetToSeq(alphabet);
      ghost var old_states := states;
      ghost var old_len := |states|;
      for ci := 0 to |chars|
        invariant |states| == |stateOf| == |expanded|
        invariant |states| >= old_len
        invariant sid < old_len <= |states|
        invariant states[0] == startExpr
        invariant states[sid] == expr
        // Old states are preserved
        invariant forall i :: 0 <= i < old_len ==> states[i] == old_states[i]
        invariant forall i :: 0 <= i < |states| ==>
          states[i] in stateOf && stateOf[states[i]] == i
        invariant forall e :: e in stateOf ==> stateOf[e] < |states|
        invariant forall e :: e in stateOf ==> states[stateOf[e]] == e
        invariant forall p :: p in trans ==> p.0 < |states| && trans[p] < |states|
        // New states are not expanded
        invariant forall i :: old_len <= i < |states| ==> !expanded[i]
        // Previously expanded states still have correct transitions
        invariant forall i, c :: 0 <= i < |states| && expanded[i] && c in alphabet ==>
          (i, c) in trans && NDeltaC(states[i], c) in stateOf &&
          trans[(i, c)] == stateOf[NDeltaC(states[i], c)]
        // Current state sid has transitions for chars processed so far
        invariant forall j :: 0 <= j < ci ==>
          (sid, chars[j]) in trans && NDeltaC(expr, chars[j]) in stateOf &&
          trans[(sid, chars[j])] == stateOf[NDeltaC(expr, chars[j])]
      {
        var c := chars[ci];
        var next := NDeltaC(expr, c);

        ghost var prev_states := states;
        ghost var prev_trans := trans;

        if next !in stateOf {
          stateOf := stateOf[next := |states|];
          states := states + [next];
          expanded := expanded + [false];
        }

        var nextId := stateOf[next];
        trans := trans[(sid, c) := nextId];
      }

      assert forall c :: c in alphabet ==>
        (sid, c) in trans && NDeltaC(expr, c) in stateOf &&
        trans[(sid, c)] == stateOf[NDeltaC(expr, c)];
      expanded := expanded[sid := true];
    }
  }

  // Build accepting set
  var accepting: set<nat> := {};
  for i := 0 to |states|
    invariant forall s :: s in accepting ==> s < |states|
    invariant forall s :: s in accepting ==> Eps(states[s])
    invariant forall s :: 0 <= s < i && Eps(states[s]) ==> s in accepting
  {
    if Eps(states[i]) {
      accepting := accepting + {i};
    }
  }

  dfa := DFA(|states|, 0, accepting, trans, states);
  DFACorrectFromMap(states, stateOf, trans, e, alphabet, accepting);
}
