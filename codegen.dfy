// Codegen: emit a self-certifying Dafny matcher from a regex.
// The output file verifies against Eps(FoldNDelta(Normalize(e, NormPlus), s, NormPlus)).

include "compile.dfy"

method Codegen(e: Exp<char>, alphabet: set<char>) returns (code: string)
  requires |alphabet| > 0
  decreases *
{
  // BFS to discover states and transitions
  var alphaSeq := SetToSeq(alphabet);
  var startExpr := Normalize(e, NormPlus);
  var states: seq<Exp<char>> := [startExpr];
  var stateOf: map<Exp<char>, nat> := map[startExpr := 0];
  var transitions: seq<(nat, char, nat)> := [];

  var frontier: seq<nat> := [0];
  while |frontier| > 0
    invariant |states| == |stateOf|
    invariant |states| > 0
    invariant forall i :: 0 <= i < |states| ==> states[i] in stateOf && stateOf[states[i]] == i
    invariant forall expr :: expr in stateOf ==> stateOf[expr] < |states|
    invariant forall f :: f in frontier ==> 0 <= f < |states|
    decreases *
  {
    assert frontier[0] in frontier;
    var sid := frontier[0];
    assert forall f :: f in frontier[1..] ==> f in frontier;
    frontier := frontier[1..];
    var expr := states[sid];
    for ci := 0 to |alphaSeq|
      invariant |states| == |stateOf|
      invariant |states| > 0
      invariant sid < |states|
      invariant forall i :: 0 <= i < |states| ==> states[i] in stateOf && stateOf[states[i]] == i
      invariant forall expr :: expr in stateOf ==> stateOf[expr] < |states|
      invariant forall f :: f in frontier ==> 0 <= f < |states|
    {
      var c := alphaSeq[ci];
      var next := NDelta(expr, c, NormPlus);
      if next !in stateOf {
        stateOf := stateOf[next := |states|];
        states := states + [next];
        frontier := frontier + [|states| - 1];
      }
      transitions := transitions + [(sid, c, stateOf[next])];
    }
  }

  var nStates := |states|;
  var n := NatToString(nStates);

  // Accepting states
  var acceptStates: seq<nat> := [];
  for i := 0 to nStates {
    if Eps(states[i]) { acceptStates := acceptStates + [i]; }
  }

  // --- Emit code ---
  var alphaForall := CharConstraint("s[i]", alphaSeq);
  var alphaParam := CharConstraint("c", alphaSeq);

  code := "// Auto-generated verified matcher\n";
  code := code + "include \"compile.dfy\"\n\n";

  // TheExpr
  code := code + "function TheExpr(): Exp<char> { " + ExpToDafny(e) + " }\n\n";

  // State expressions
  for i := 0 to nStates {
    code := code + "function S" + NatToString(i) + "(): Exp<char> { " + ExpToDafny(states[i]) + " }\n";
  }

  // Trans function
  code := code + "\nfunction Trans(state: nat, c: char): nat\n";
  code := code + "  requires state < " + n + " && (" + alphaParam + ")\n";
  code := code + "  ensures Trans(state, c) < " + n + "\n";
  code := code + "{\n";
  for ti := 0 to |transitions| {
    var src := transitions[ti].0;
    var c := transitions[ti].1;
    var dst := transitions[ti].2;
    var kw := if ti == 0 then "  if" else "  else if";
    code := code + kw + " state == " + NatToString(src) + " && c == '" + [c] + "' then " + NatToString(dst) + "\n";
  }
  code := code + "  else 0\n}\n";

  // Accept predicate
  code := code + "\npredicate Accept(state: nat) requires state < " + n + " {\n  ";
  if |acceptStates| == 0 {
    code := code + "false";
  } else {
    for ai := 0 to |acceptStates| {
      if ai > 0 { code := code + " || "; }
      code := code + "state == " + NatToString(acceptStates[ai]);
    }
  }
  code := code + "\n}\n";

  // FoldTrans
  code := code + "\nfunction FoldTrans(state: nat, s: seq<char>): nat\n";
  code := code + "  requires state < " + n + "\n";
  code := code + "  requires forall i :: 0 <= i < |s| ==> " + alphaForall + "\n";
  code := code + "  ensures FoldTrans(state, s) < " + n + "\n";
  code := code + "  decreases |s|\n";
  code := code + "{ if |s| == 0 then state else FoldTrans(Trans(state, s[0]), s[1..]) }\n";

  // StateExpr (ghost)
  code := code + "\nghost function StateExpr(state: nat): Exp<char>\n";
  code := code + "  requires state < " + n + "\n";
  code := code + "{\n";
  for i := 0 to nStates {
    var kw := if i == 0 then "  if" else "  else if";
    if i < nStates - 1 {
      code := code + kw + " state == " + NatToString(i) + " then S" + NatToString(i) + "()\n";
    } else {
      code := code + "  else S" + NatToString(i) + "()\n";
    }
  }
  code := code + "}\n";

  // TransCorrect lemma
  code := code + "\nlemma TransCorrect(state: nat, c: char)\n";
  code := code + "  requires state < " + n + " && (" + alphaParam + ")\n";
  code := code + "  ensures NDelta(StateExpr(state), c, NormPlus) == StateExpr(Trans(state, c))\n";
  code := code + "{}\n";

  // AcceptCorrect lemma
  code := code + "\nlemma AcceptCorrect(state: nat)\n";
  code := code + "  requires state < " + n + "\n";
  code := code + "  ensures Accept(state) == Eps(StateExpr(state))\n";
  code := code + "{}\n";

  // NormStart lemma
  code := code + "\nlemma NormStart() ensures Normalize(TheExpr(), NormPlus) == S0() {}\n";

  // FoldTransCorrect lemma
  code := code + "\nlemma FoldTransCorrect(state: nat, s: seq<char>)\n";
  code := code + "  requires state < " + n + "\n";
  code := code + "  requires forall i :: 0 <= i < |s| ==> " + alphaForall + "\n";
  code := code + "  ensures StateExpr(FoldTrans(state, s)) == FoldNDelta(StateExpr(state), s, NormPlus)\n";
  code := code + "  decreases |s|\n";
  code := code + "{\n";
  code := code + "  if |s| != 0 {\n";
  code := code + "    TransCorrect(state, s[0]);\n";
  code := code + "    FoldTransCorrect(Trans(state, s[0]), s[1..]);\n";
  code := code + "  }\n";
  code := code + "}\n";

  // CorrectnessNDelta lemma
  code := code + "\nlemma CorrectnessNDelta(s: seq<char>)\n";
  code := code + "  requires forall i :: 0 <= i < |s| ==> " + alphaForall + "\n";
  code := code + "  ensures Accept(FoldTrans(0, s)) == Eps(FoldNDelta(Normalize(TheExpr(), NormPlus), s, NormPlus))\n";
  code := code + "{\n";
  code := code + "  NormStart();\n";
  code := code + "  FoldTransCorrect(0, s);\n";
  code := code + "  AcceptCorrect(FoldTrans(0, s));\n";
  code := code + "}\n";

  // RunDFA method
  code := code + "\nmethod RunDFA(s: seq<char>) returns (state: nat)\n";
  code := code + "  requires forall i :: 0 <= i < |s| ==> " + alphaForall + "\n";
  code := code + "  ensures state < " + n + "\n";
  code := code + "  ensures state == FoldTrans(0, s)\n";
  code := code + "{\n";
  code := code + "  state := 0;\n";
  code := code + "  for i := 0 to |s|\n";
  code := code + "    invariant 0 <= state < " + n + "\n";
  code := code + "    invariant FoldTrans(state, s[i..]) == FoldTrans(0, s)\n";
  code := code + "  {\n";
  code := code + "    assert s[i..] == [s[i]] + s[i+1..];\n";
  code := code + "    state := Trans(state, s[i]);\n";
  code := code + "  }\n";
  code := code + "  assert s[|s|..] == [];\n";
  code := code + "}\n";

  // MatchSpecialized method
  code := code + "\nmethod MatchSpecialized(s: seq<char>) returns (accepts: bool)\n";
  code := code + "  requires forall i :: 0 <= i < |s| ==> " + alphaForall + "\n";
  code := code + "  ensures accepts == Eps(FoldNDelta(Normalize(TheExpr(), NormPlus), s, NormPlus))\n";
  code := code + "{\n";
  code := code + "  var state := RunDFA(s);\n";
  code := code + "  accepts := Accept(state);\n";
  code := code + "  CorrectnessNDelta(s);\n";
  code := code + "}\n";
}

// --- Helpers ---

function ExpToDafny(e: Exp<char>): string {
  match e
  case Zero => "Zero"
  case One => "One"
  case Char(a) => "Char('" + [a] + "')"
  case Plus(e1, e2) => "Plus(" + ExpToDafny(e1) + ", " + ExpToDafny(e2) + ")"
  case Comp(e1, e2) => "Comp(" + ExpToDafny(e1) + ", " + ExpToDafny(e2) + ")"
  case Star(e1) => "Star(" + ExpToDafny(e1) + ")"
}

function NatToString(n: nat): string {
  if n < 10 then [('0' as int + n) as char]
  else NatToString(n / 10) + [('0' as int + (n % 10)) as char]
}

function CharConstraint(v: string, alpha: seq<char>): string
  requires |alpha| > 0
{
  if |alpha| == 1 then v + " == '" + [alpha[0]] + "'"
  else v + " == '" + [alpha[0]] + "' || " + CharConstraint(v, alpha[1..])
}
