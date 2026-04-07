// DFA compilation via BFS over normalized Brzozowski derivatives.
// Given a regex and a finite alphabet, builds a transition table.
// Matching is then a single table-driven loop: O(|input|), O(1) per char.

include "normalize.dfy"
include "walk.dfy"

/** A compiled DFA: states 0..nStates-1, transition table, accepting set. */
datatype DFA = DFA(
  nStates: nat,
  start: nat,
  accepting: set<nat>,
  trans: map<(nat, char), nat>
)

/** Whether a DFA is well-formed for a given alphabet. */
ghost predicate WellFormedDFA(dfa: DFA, alphabet: set<char>) {
  && dfa.nStates > 0
  && dfa.start < dfa.nStates
  && (forall s :: s in dfa.accepting ==> s < dfa.nStates)
  && (forall st, c :: 0 <= st < dfa.nStates && c in alphabet ==>
       (st, c) in dfa.trans && dfa.trans[(st, c)] < dfa.nStates)
}

/** Imperative DFA matcher: follow the transition table. O(|s|) time. */
method DFAMatch(dfa: DFA, s: seq<char>, alphabet: set<char>) returns (accepts: bool)
  requires WellFormedDFA(dfa, alphabet)
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
{
  var state := dfa.start;
  for i := 0 to |s|
    invariant 0 <= state < dfa.nStates
  {
    state := dfa.trans[(state, s[i])];
  }
  accepts := state in dfa.accepting;
}

/** Convert a set to a sequence. */
method SetToSeq(s: set<char>) returns (sq: seq<char>)
  ensures |sq| == |s|
  ensures forall c :: c in s <==> c in sq
{
  sq := [];
  var remaining := s;
  while |remaining| > 0
    invariant remaining <= s
    invariant |sq| + |remaining| == |s|
    invariant forall c :: c in sq <==> c in s && c !in remaining
  {
    var c :| c in remaining;
    sq := sq + [c];
    remaining := remaining - {c};
  }
}

/** Compile a regex over a finite alphabet into a DFA.
    BFS explores normalized derivative states until fixpoint.
    Uses decreases * as finiteness of derivative classes is not proven here. */
method Compile(e: Exp<char>, alphabet: set<char>) returns (dfa: DFA)
  requires |alphabet| > 0
  decreases *
  ensures WellFormedDFA(dfa, alphabet)
{
  var alphaSeq := SetToSeq(alphabet);

  var startExpr := Normalize(e);
  var states: seq<Exp<char>> := [startExpr];
  var stateOf: map<Exp<char>, nat> := map[startExpr := 0];
  var trans: map<(nat, char), nat> := map[];

  // expanded[i] == true means state i has had its transitions computed
  var expanded: seq<bool> := [false];

  // Process states until all are expanded
  var done := false;
  while !done
    invariant |states| == |stateOf| == |expanded|
    invariant |states| > 0
    invariant forall i :: 0 <= i < |states| ==>
      states[i] in stateOf && stateOf[states[i]] == i
    invariant forall expr :: expr in stateOf ==> stateOf[expr] < |states|
    invariant forall p :: p in trans ==> p.0 < |states| && trans[p] < |states|
    invariant forall i, c :: 0 <= i < |states| && expanded[i] && c in alphabet ==>
      (i, c) in trans
    invariant done ==> forall i :: 0 <= i < |expanded| ==> expanded[i]
    decreases *
  {
    // Find an unexpanded state
    var found := -1;
    for i := 0 to |expanded|
      invariant forall j :: 0 <= j < i ==> expanded[j]
      invariant found == -1
    {
      if !expanded[i] {
        found := i;
        break;
      }
    }

    if found == -1 {
      done := true;
    } else {
      var sid := found;
      var expr := states[sid];

      for ci := 0 to |alphaSeq|
        invariant |states| == |stateOf| == |expanded|
        invariant |states| > 0
        invariant sid < |states|
        invariant forall i :: 0 <= i < |states| ==>
          states[i] in stateOf && stateOf[states[i]] == i
        invariant forall expr :: expr in stateOf ==> stateOf[expr] < |states|
        invariant forall p :: p in trans ==> p.0 < |states| && trans[p] < |states|
        invariant forall i, c :: 0 <= i < |states| && expanded[i] && c in alphabet ==>
          (i, c) in trans
        invariant forall j :: 0 <= j < ci ==> (sid, alphaSeq[j]) in trans
      {
        var c := alphaSeq[ci];
        var next := Normalize(Delta(expr)(c));

        if next !in stateOf {
          var nextId := |states|;
          stateOf := stateOf[next := nextId];
          states := states + [next];
          expanded := expanded + [false];
        }

        var nextId := stateOf[next];
        trans := trans[(sid, c) := nextId];
      }

      assert forall c :: c in alphabet ==> (sid, c) in trans;
      expanded := expanded[sid := true];
    }
  }

  // Build accepting set
  var accepting: set<nat> := {};
  for i := 0 to |states|
    invariant forall s :: s in accepting ==> s < |states|
  {
    if Eps(states[i]) {
      accepting := accepting + {i};
    }
  }

  dfa := DFA(|states|, 0, accepting, trans);
}
