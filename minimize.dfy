// DFA minimization via Moore's algorithm.
// Proven correct: Minimize preserves the accepted language.

include "compile.dfy"

datatype Signature = Sig(cls: nat, succs: seq<nat>)

function ComputeSuccClasses(dfa: DFA, partition: seq<nat>, state: nat, alphaSeq: seq<char>, idx: nat): seq<nat>
  requires |partition| == dfa.nStates && state < dfa.nStates && idx <= |alphaSeq|
  requires forall i, c :: 0 <= i < dfa.nStates && c in alphaSeq ==>
    (i, c) in dfa.trans && dfa.trans[(i, c)] < dfa.nStates
  decreases |alphaSeq| - idx
{
  if idx == |alphaSeq| then []
  else [partition[dfa.trans[(state, alphaSeq[idx])]]] + ComputeSuccClasses(dfa, partition, state, alphaSeq, idx + 1)
}

function ComputeSignature(dfa: DFA, partition: seq<nat>, state: nat, alphaSeq: seq<char>): Signature
  requires |partition| == dfa.nStates && state < dfa.nStates
  requires forall i, c :: 0 <= i < dfa.nStates && c in alphaSeq ==>
    (i, c) in dfa.trans && dfa.trans[(i, c)] < dfa.nStates
{
  Sig(partition[state], ComputeSuccClasses(dfa, partition, state, alphaSeq, 0))
}

lemma ComputeSuccClassesCorrect(dfa: DFA, partition: seq<nat>, state: nat, alphaSeq: seq<char>, idx: nat, ci: nat)
  requires |partition| == dfa.nStates && state < dfa.nStates && idx <= |alphaSeq|
  requires forall i, c :: 0 <= i < dfa.nStates && c in alphaSeq ==>
    (i, c) in dfa.trans && dfa.trans[(i, c)] < dfa.nStates
  requires idx <= ci < |alphaSeq|
  ensures ci - idx < |ComputeSuccClasses(dfa, partition, state, alphaSeq, idx)|
  ensures ComputeSuccClasses(dfa, partition, state, alphaSeq, idx)[ci - idx] == partition[dfa.trans[(state, alphaSeq[ci])]]
  decreases ci - idx
{
  if ci > idx { ComputeSuccClassesCorrect(dfa, partition, state, alphaSeq, idx + 1, ci); }
}

method InitPartition(dfa: DFA) returns (partition: seq<nat>, numClasses: nat, repr: seq<nat>)
  requires dfa.nStates > 0
  ensures |partition| == dfa.nStates
  ensures numClasses >= 1 && numClasses <= dfa.nStates
  ensures forall i :: 0 <= i < dfa.nStates ==> partition[i] < numClasses
  ensures forall i, j :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j] ==>
    (i in dfa.accepting <==> j in dfa.accepting)
  ensures |repr| == numClasses
  ensures forall c :: 0 <= c < numClasses ==> repr[c] < dfa.nStates && partition[repr[c]] == c
{
  var hasAcc := false;
  var hasNonAcc := false;
  partition := [];
  for k := 0 to dfa.nStates
    invariant |partition| == k
    invariant forall i :: 0 <= i < k ==> partition[i] == (if i in dfa.accepting then 1 else 0)
    invariant hasAcc <==> exists i :: 0 <= i < k && i in dfa.accepting
    invariant hasNonAcc <==> exists i :: 0 <= i < k && i !in dfa.accepting
  {
    if k in dfa.accepting { partition := partition + [1]; hasAcc := true; }
    else { partition := partition + [0]; hasNonAcc := true; }
  }
  if hasAcc && hasNonAcc {
    numClasses := 2;
    var a :| 0 <= a < dfa.nStates && a in dfa.accepting;
    var b :| 0 <= b < dfa.nStates && b !in dfa.accepting;
    repr := [b, a]; // repr[0] = non-accepting, repr[1] = accepting
  } else if hasAcc {
    numClasses := 1;
    partition := seq(dfa.nStates, _ => 0);
    repr := [0];
  } else {
    numClasses := 1;
    repr := [0];
  }
}

method AssignClasses(sigs: seq<Signature>, n: nat)
    returns (newPartition: seq<nat>, numNew: nat, classFirst: seq<nat>)
  requires |sigs| == n
  ensures |newPartition| == n
  ensures numNew <= n
  ensures n > 0 ==> numNew >= 1
  ensures forall i :: 0 <= i < n ==> newPartition[i] < numNew
  ensures forall i, j :: 0 <= i < n && 0 <= j < n && newPartition[i] == newPartition[j] ==> sigs[i] == sigs[j]
  ensures |classFirst| == numNew
  ensures forall c :: 0 <= c < numNew ==> classFirst[c] < n && newPartition[classFirst[c]] == c
{
  var sigToClass: map<Signature, nat> := map[];
  var nextClass: nat := 0;
  newPartition := [];
  classFirst := [];

  for k := 0 to n
    invariant |newPartition| == k
    invariant nextClass <= k && nextClass <= n
    invariant |classFirst| == nextClass
    invariant forall i :: 0 <= i < k ==> newPartition[i] < nextClass
    invariant forall sig :: sig in sigToClass ==> sigToClass[sig] < nextClass
    invariant forall i :: 0 <= i < k ==> sigs[i] in sigToClass && newPartition[i] == sigToClass[sigs[i]]
    invariant forall s1, s2 :: s1 in sigToClass && s2 in sigToClass && sigToClass[s1] == sigToClass[s2] ==> s1 == s2
    invariant forall c :: 0 <= c < nextClass ==> classFirst[c] < k && newPartition[classFirst[c]] == c
  {
    var sig := sigs[k];
    if sig in sigToClass {
      newPartition := newPartition + [sigToClass[sig]];
    } else {
      sigToClass := sigToClass[sig := nextClass];
      newPartition := newPartition + [nextClass];
      classFirst := classFirst + [k];
      nextClass := nextClass + 1;
    }
  }
  numNew := nextClass;
  if n > 0 { assert newPartition[0] < nextClass; }
}

method RefinePartition(dfa: DFA, partition: seq<nat>, alphaSeq: seq<char>)
    returns (newPartition: seq<nat>, newNumClasses: nat, newRepr: seq<nat>)
  requires |partition| == dfa.nStates && dfa.nStates > 0
  requires forall i :: 0 <= i < dfa.nStates ==> partition[i] < dfa.nStates
  requires forall i, c :: 0 <= i < dfa.nStates && c in alphaSeq ==>
    (i, c) in dfa.trans && dfa.trans[(i, c)] < dfa.nStates
  ensures |newPartition| == dfa.nStates
  ensures newNumClasses <= dfa.nStates
  ensures forall i :: 0 <= i < dfa.nStates ==> newPartition[i] < newNumClasses
  ensures forall i, j :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && newPartition[i] == newPartition[j] ==>
    partition[i] == partition[j]
  ensures forall i, j :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && newPartition[i] == newPartition[j] ==>
    forall ci :: 0 <= ci < |alphaSeq| ==>
      partition[dfa.trans[(i, alphaSeq[ci])]] == partition[dfa.trans[(j, alphaSeq[ci])]]
  ensures |newRepr| == newNumClasses
  ensures forall c :: 0 <= c < newNumClasses ==> newRepr[c] < dfa.nStates && newPartition[newRepr[c]] == c
{
  var sigs: seq<Signature> := [];
  for k := 0 to dfa.nStates
    invariant |sigs| == k
    invariant forall i :: 0 <= i < k ==> sigs[i] == ComputeSignature(dfa, partition, i, alphaSeq)
  {
    sigs := sigs + [ComputeSignature(dfa, partition, k, alphaSeq)];
  }

  var classFirst: seq<nat>;
  newPartition, newNumClasses, classFirst := AssignClasses(sigs, dfa.nStates);
  newRepr := classFirst;

  forall i, j | 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && newPartition[i] == newPartition[j]
    ensures partition[i] == partition[j]
  { assert sigs[i] == sigs[j]; }

  forall i, j | 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && newPartition[i] == newPartition[j]
    ensures forall ci :: 0 <= ci < |alphaSeq| ==>
      partition[dfa.trans[(i, alphaSeq[ci])]] == partition[dfa.trans[(j, alphaSeq[ci])]]
  {
    assert sigs[i] == sigs[j];
    forall ci | 0 <= ci < |alphaSeq|
      ensures partition[dfa.trans[(i, alphaSeq[ci])]] == partition[dfa.trans[(j, alphaSeq[ci])]]
    {
      ComputeSuccClassesCorrect(dfa, partition, i, alphaSeq, 0, ci);
      ComputeSuccClassesCorrect(dfa, partition, j, alphaSeq, 0, ci);
    }
  }
}

lemma FindInSeq(alphaSeq: seq<char>, c: char)
  requires c in alphaSeq
  ensures exists ci :: 0 <= ci < |alphaSeq| && alphaSeq[ci] == c
{}

method {:isolate_assertions} {:verification_time_limit 90} BuildMinDFA(
    dfa: DFA, partition: seq<nat>, numClasses: nat, repr: seq<nat>, alphaSeq: seq<char>)
    returns (minDfa: DFA)
  requires WellFormedDFA(dfa, set c | c in alphaSeq)
  requires |partition| == dfa.nStates && dfa.nStates > 0
  requires numClasses >= 1 && numClasses <= dfa.nStates
  requires forall i :: 0 <= i < dfa.nStates ==> partition[i] < numClasses
  requires |repr| == numClasses
  requires forall c :: 0 <= c < numClasses ==> repr[c] < dfa.nStates && partition[repr[c]] == c
  requires forall i, j {:trigger partition[i], partition[j]} :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j] ==>
    (i in dfa.accepting <==> j in dfa.accepting)
  requires forall i, j {:trigger partition[i], partition[j]} :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j] ==>
    forall c :: c in alphaSeq ==> partition[dfa.trans[(i, c)]] == partition[dfa.trans[(j, c)]]
  ensures WellFormedDFA(minDfa, set c | c in alphaSeq)
  ensures minDfa.nStates == numClasses
  ensures minDfa.start == partition[dfa.start]
  ensures forall s :: 0 <= s < dfa.nStates ==>
    (s in dfa.accepting <==> partition[s] in minDfa.accepting)
  ensures forall s, c :: 0 <= s < dfa.nStates && c in alphaSeq ==>
    (partition[s], c) in minDfa.trans && minDfa.trans[(partition[s], c)] == partition[dfa.trans[(s, c)]]
{
  var alphabet := set c | c in alphaSeq;

  var accepting: set<nat> := {};
  for c := 0 to numClasses
    invariant forall cc :: cc in accepting ==> cc < numClasses
    invariant forall cc :: 0 <= cc < c && repr[cc] in dfa.accepting ==> cc in accepting
    invariant forall cc :: cc in accepting ==> repr[cc] in dfa.accepting
  {
    if repr[c] in dfa.accepting { accepting := accepting + {c}; }
  }

  var trans: map<(nat, char), nat> := map[];
  for c := 0 to numClasses
    invariant forall p :: p in trans ==> p.0 < numClasses && trans[p] < numClasses
    invariant forall cc, ch :: 0 <= cc < c && ch in alphaSeq ==>
      (cc, ch) in trans && trans[(cc, ch)] == partition[dfa.trans[(repr[cc], ch)]]
  {
    for ci := 0 to |alphaSeq|
      invariant forall p :: p in trans ==> p.0 < numClasses && trans[p] < numClasses
      invariant forall cc, ch :: 0 <= cc < c && ch in alphaSeq ==>
        (cc, ch) in trans && trans[(cc, ch)] == partition[dfa.trans[(repr[cc], ch)]]
      invariant forall cii :: 0 <= cii < ci ==>
        (c, alphaSeq[cii]) in trans && trans[(c, alphaSeq[cii])] == partition[dfa.trans[(repr[c], alphaSeq[cii])]]
    {
      trans := trans[(c, alphaSeq[ci]) := partition[dfa.trans[(repr[c], alphaSeq[ci])]]];
    }
  }

  minDfa := DFA(numClasses, partition[dfa.start], accepting, trans,
    seq(numClasses, _ => Zero));

  assert minDfa.nStates == |minDfa.exprs|;
  assert minDfa.start < minDfa.nStates;

  forall s, ch | 0 <= s < dfa.nStates && ch in alphaSeq
    ensures (partition[s], ch) in minDfa.trans && minDfa.trans[(partition[s], ch)] == partition[dfa.trans[(s, ch)]]
  {
    var c := partition[s];
    var r := repr[c];
    assert partition[r] == c;
    assert partition[dfa.trans[(r, ch)]] == partition[dfa.trans[(s, ch)]];
  }

  forall s | 0 <= s < dfa.nStates
    ensures s in dfa.accepting <==> partition[s] in minDfa.accepting
  {
    var c := partition[s];
    var r := repr[c];
    assert partition[r] == c;
  }
}

method MooreRefine(dfa: DFA, alphaSeq: seq<char>)
    returns (partition: seq<nat>, numClasses: nat, repr: seq<nat>)
  requires WellFormedDFA(dfa, set c | c in alphaSeq)
  requires |alphaSeq| > 0
  decreases *
  ensures |partition| == dfa.nStates
  ensures numClasses >= 1 && numClasses <= dfa.nStates
  ensures forall i :: 0 <= i < dfa.nStates ==> partition[i] < numClasses
  ensures forall i, j {:trigger partition[i], partition[j]} :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j] ==>
    (i in dfa.accepting <==> j in dfa.accepting)
  ensures forall i, j {:trigger partition[i], partition[j]} :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j] ==>
    forall c :: c in alphaSeq ==> partition[dfa.trans[(i, c)]] == partition[dfa.trans[(j, c)]]
  ensures |repr| == numClasses
  ensures forall c :: 0 <= c < numClasses ==> repr[c] < dfa.nStates && partition[repr[c]] == c
{
  partition, numClasses, repr := InitPartition(dfa);

  var done := false;
  while !done
    invariant |partition| == dfa.nStates
    invariant numClasses >= 1 && numClasses <= dfa.nStates
    invariant forall i :: 0 <= i < dfa.nStates ==> partition[i] < numClasses
    invariant forall i, j {:trigger partition[i], partition[j]} :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j] ==>
      (i in dfa.accepting <==> j in dfa.accepting)
    invariant done ==> forall i, j {:trigger partition[i], partition[j]} :: 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j] ==>
      forall ci :: 0 <= ci < |alphaSeq| ==> partition[dfa.trans[(i, alphaSeq[ci])]] == partition[dfa.trans[(j, alphaSeq[ci])]]
    invariant |repr| == numClasses
    invariant forall c :: 0 <= c < numClasses ==> repr[c] < dfa.nStates && partition[repr[c]] == c
    decreases *
  {
    var newPartition: seq<nat>;
    var newNumClasses: nat;
    var newRepr: seq<nat>;
    newPartition, newNumClasses, newRepr := RefinePartition(dfa, partition, alphaSeq);
    if newPartition == partition {
      done := true;
    } else {
      partition := newPartition;
      numClasses := newNumClasses;
      repr := newRepr;
    }
  }
  forall i, j {:trigger partition[i], partition[j]} | 0 <= i < dfa.nStates && 0 <= j < dfa.nStates && partition[i] == partition[j]
    ensures forall c :: c in alphaSeq ==> partition[dfa.trans[(i, c)]] == partition[dfa.trans[(j, c)]]
  {
    forall c | c in alphaSeq
      ensures partition[dfa.trans[(i, c)]] == partition[dfa.trans[(j, c)]]
    { FindInSeq(alphaSeq, c); }
  }
}

lemma DFARunCommutes(dfa: DFA, minDfa: DFA, partition: seq<nat>, s: seq<char>, state: nat, alphabet: set<char>)
  requires WellFormedDFA(dfa, alphabet) && WellFormedDFA(minDfa, alphabet)
  requires |partition| == dfa.nStates && state < dfa.nStates
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
  requires forall st :: 0 <= st < dfa.nStates ==> partition[st] < minDfa.nStates
  requires forall st :: 0 <= st < dfa.nStates ==>
    (st in dfa.accepting <==> partition[st] in minDfa.accepting)
  requires forall st, c :: 0 <= st < dfa.nStates && c in alphabet ==>
    (partition[st], c) in minDfa.trans && minDfa.trans[(partition[st], c)] == partition[dfa.trans[(st, c)]]
  ensures DFARun(minDfa, s, partition[state], alphabet) == DFARun(dfa, s, state, alphabet)
  decreases |s|
{
  if |s| > 0 {
    var next := dfa.trans[(state, s[0])];
    assert minDfa.trans[(partition[state], s[0])] == partition[next];
    DFARunCommutes(dfa, minDfa, partition, s[1..], next, alphabet);
  }
}

lemma AlphaSeqIsAlphabet(alphaSeq: seq<char>, alphabet: set<char>)
  requires |alphaSeq| == |alphabet|
  requires forall c :: c in alphabet <==> c in alphaSeq
  ensures (set c | c in alphaSeq) == alphabet
{
  var s := set c | c in alphaSeq;
  forall c ensures c in s <==> c in alphabet {}
}

method {:verification_time_limit 120} {:isolate_assertions} Minimize(dfa: DFA, alphabet: set<char>) returns (minDfa: DFA)
  requires WellFormedDFA(dfa, alphabet)
  requires |alphabet| > 0
  decreases *
  ensures WellFormedDFA(minDfa, alphabet)
{
  var alphaSeq := SetToSeq(alphabet);
  AlphaSeqIsAlphabet(alphaSeq, alphabet);
  var repr: seq<nat>;
  var partition: seq<nat>;
  var numClasses: nat;
  partition, numClasses, repr := MooreRefine(dfa, alphaSeq);
  minDfa := BuildMinDFA(dfa, partition, numClasses, repr, alphaSeq);
}

lemma MinimizePreservesLanguage(dfa: DFA, minDfa: DFA, partition: seq<nat>, e: Exp<char>, s: seq<char>, alphabet: set<char>)
  requires DFACorrect(dfa, e, alphabet)
  requires WellFormedDFA(minDfa, alphabet)
  requires |partition| == dfa.nStates
  requires forall i :: 0 <= i < |s| ==> s[i] in alphabet
  requires minDfa.start == partition[dfa.start]
  requires forall st :: 0 <= st < dfa.nStates ==> partition[st] < minDfa.nStates
  requires forall st :: 0 <= st < dfa.nStates ==>
    (st in dfa.accepting <==> partition[st] in minDfa.accepting)
  requires forall st, c :: 0 <= st < dfa.nStates && c in alphabet ==>
    (partition[st], c) in minDfa.trans && minDfa.trans[(partition[st], c)] == partition[dfa.trans[(st, c)]]
  ensures DFAAccepts(minDfa, s, alphabet) == DFAAccepts(dfa, s, alphabet)
{
  DFARunCommutes(dfa, minDfa, partition, s, dfa.start, alphabet);
}
