# dafny-re: a guided tutorial

This tutorial walks you through the dafny-re artifact end to end. You don't need to understand every lemma. The goal is to follow one clean verified transformation and see why each step is trustworthy:

```text
regular expression AST
  -> derivative matcher
  -> normalized residual states
  -> DFA table
  -> generated specialized matcher
```

Keep one idea in mind the whole way through:

> The generated matcher runs on integers, but the proof remembers what regex residual each integer state means.

## 0. Setup

Read the files in this order. Open each one in your editor as you reach the corresponding section:

1. `gen_star_ab_a.dfy` — start with the payoff
2. `re.dfy` — source language and derivative semantics
3. `walk.dfy` / `match.dfy` — on-the-fly verified matcher
4. `normalize.dfy` / `bridge.dfy` — normalization and the semantic bridge
5. `compile.dfy` — DFA correctness invariant
6. `codegen.dfy` — generator that emits a self-certifying file
7. `test.dfy` — optional runtime smoke test

Useful commands you can run as you go:

```sh
# Main payoff: generated matcher verifies independently
dafny verify gen_star_ab_a.dfy

# Optional: run the generated example (Main lives in the demo, not the generated file)
dafny run demo_star_ab_a.dfy

# Optional: verify the whole artifact
dafny verify re.dfy walk.dfy match.dfy normalize.dfy bridge.dfy compile.dfy minimize.dfy parse.dfy codegen.dfy gen_star_ab_a.dfy

# Optional: run derivative matcher + compiled DFA smoke tests
dafny run test.dfy --target cs --no-verify
```

If you only have a minute, jump to [Section 12](#12-one-minute-version).

## 1. Start with the generated artifact

Open `gen_star_ab_a.dfy`.

This file is generated for the regular expression `(a|b)*a`. It is a specialized matcher, but it also contains enough proof structure for Dafny to check that the matcher implements the derivative semantics of the source regex.

Find the source expression it was built from:

```dafny
function TheExpr(): Exp<char> {
  Comp(Star(Plus(Char('a'), Char('b'))), Char('a'))
}
```

Now look at the two states:

```dafny
function S0(): Exp<char> { ... }
function S1(): Exp<char> { ... }
```

They mean:

```text
state 0 ↦ (a|b)*a
state 1 ↦ (a|b)*a + ε
```

State 1 is accepting because its residual regex accepts the empty string. Intuitively: state 1 means "the prefix read so far ends in `a`."

Next, find the actual runtime transition function:

```dafny
function Trans(state: nat, c: char): nat
  requires state < 2 && (c == 'a' || c == 'b')
  ensures Trans(state, c) < 2
{
  if state == 0 && c == 'a' then 1
  else if state == 1 && c == 'a' then 1
  else 0
}
```

Notice how small the executable story is: two numeric states and a transition function. The proof story is what explains why these numbers are the right states.

## 2. The ghost meaning of states

Still in `gen_star_ab_a.dfy`, find:

```dafny
ghost function StateExpr(state: nat): Exp<char>
  requires state < 2
{ if state == 0 then S0() else S1() }
```

This is the ghost interpretation of the target program. Runtime states are `nat`s. Proof states are residual regular expressions.

Now look at the two local certificate lemmas:

```dafny
lemma TransCorrect(state: nat, c: char)
  requires state < 2 && (c == 'a' || c == 'b')
  ensures NDelta(StateExpr(state), c, NormPlus) == StateExpr(Trans(state, c))
{}

lemma AcceptCorrect(state: nat)
  requires state < 2
  ensures Accept(state) == Eps(StateExpr(state))
{}
```

`TransCorrect` says that a numeric transition agrees with the derivative transition. `AcceptCorrect` says that a numeric accepting state agrees with `Eps` of the residual regex.

This is the key invariant to hold onto:

```text
meaning(Trans(q, c)) = normalize(Delta(meaning(q), c))
Accept(q)            = Eps(meaning(q))
```

## 3. The loop invariant in the generated matcher

Still in `gen_star_ab_a.dfy`, find the executable matcher loop:

```dafny
method RunDFA(s: seq<char>) returns (state: nat)
  ensures state == FoldTrans(0, s)
{
  state := 0;
  for i := 0 to |s|
    invariant 0 <= state < 2
    invariant FoldTrans(state, s[i..]) == FoldTrans(0, s)
  {
    state := Trans(state, s[i]);
  }
}
```

Read the invariant carefully: running from the current state over the remaining suffix is equivalent to running from the start over the whole string.

Then find:

```dafny
lemma FoldTransCorrect(state: nat, s: seq<char>)
  ensures StateExpr(FoldTrans(state, s))
       == FoldNDelta(StateExpr(state), s, NormPlus)
```

Folding numeric transitions tracks folding normalized derivatives. That is the bridge from the target program back to the source-level semantics.

Finally, find the top-level specialized matcher:

```dafny
method MatchSpecialized(s: seq<char>) returns (accepts: bool)
  ensures accepts == Eps(FoldNDelta(Normalize(TheExpr(), NormPlus), s, NormPlus))
```

The generated file proves the matcher agrees with normalized derivative semantics. The next sections show why normalized derivative semantics agrees with the original regex semantics.

> Note: the generated file deliberately stops at the derivative-level postcondition. For a cleaner top-level theorem, compose with `FoldNDeltaCorrect` at the use site to get `accepts == Matches(TheExpr(), s)`. This is kept outside the generated file so callers that don't need `Matches` avoid its heavier `Walk`/`Denotational` unfolding. (The README has the three-line snippet.)

## 4. Step backward: the paper spine in `re.dfy`

Open `re.dfy`.

Find the source language:

```dafny
datatype Exp<A> =
  | Zero | One | Char(A)
  | Plus(Exp, Exp)
  | Comp(Exp, Exp)
  | Star(Exp)
```

This is the source language: regular expressions as an inductive datatype.

Look at the language semantics:

```dafny
codatatype Lang<!A> = Alpha(eps: bool, delta: A -> Lang<A>)
```

Languages are represented coalgebraically: can they accept empty, and how do they step on one character?

Then find:

```dafny
function Eps<A>(e: Exp): bool { ... }
function Delta<A(==)>(e: Exp, a: A): Exp { ... }
```

This equips regular expressions themselves with the structure of a DFA. `Eps(e)` is acceptingness; `Delta(e,a)` is the next state.

Now find the main theorem from the paper foundation:

```dafny
lemma OperationalAndDenotationalAreBisimilar<A(!new)>(e: Exp)
  ensures Bisimilar<A>(Operational(e), Denotational(e))
```

This is the semantic foundation: the operational derivative view and the denotational language view agree.

Don't get stuck on the coalgebra here. The one-line version is enough to keep going:

```text
Denotational: what language does the regex mean?
Operational: how does the regex step?
The theorem: these agree.
```

## 5. The first executable matcher

Open `walk.dfy`, then `match.dfy`.

In `walk.dfy`, find:

```dafny
function FoldDelta<A(==)>(e: Exp<A>, s: seq<A>): Exp<A>

ghost predicate Matches<A(!new)>(e: Exp<A>, s: seq<A>) {
  Walk(Denotational(e), s).eps
}

lemma MatchesEquivFoldDelta<A(!new)>(e: Exp, s: seq<A>)
  ensures Matches(e, s) == Eps(FoldDelta(e, s))
```

`Matches` is the denotational spec. `FoldDelta` is the executable derivative computation. This lemma says they agree.

In `match.dfy`, find:

```dafny
method Match(e: Exp<char>, s: seq<char>) returns (accepts: bool)
  ensures accepts == Matches(e, s)
{
  var current := e;
  for i := 0 to |s|
    invariant current == FoldDelta(e, s[..i])
  {
    current := Delta(current, s[i]);
  }
  accepts := Eps(current);
}
```

Before compiling to a DFA table, you already have a verified no-backtracking matcher: fold derivatives over the input, then check `Eps`.

## 6. Why normalization is safe

Open `normalize.dfy`.

Find:

```dafny
function Normalize<A(==)>(e: Exp<A>, normPlus: ...): Exp<A> { ... }
function NDelta<A(==)>(e: Exp<A>, a: A, normPlus: ...): Exp<A> {
  Normalize(Delta(e, a), normPlus)
}
```

Raw derivatives can grow and produce many syntactically different expressions for the same language. Normalization collapses residuals before you treat them as DFA states.

Find:

```dafny
lemma NormalizeCorrect<A(!new)>(e: Exp, normPlus: ...)
  requires NormPlusSpec<A>(normPlus)
  ensures Bisimilar<A>(Denotational(Normalize(e, normPlus)), Denotational(e))
```

Normalization is not a trusted optimization. It is proved language-preserving.

Open `bridge.dfy` and find:

```dafny
lemma FoldNDeltaCorrect<A(!new)>(e: Exp, s: seq<A>, normPlus: ...)
  requires NormPlusSpec<A>(normPlus)
  ensures Eps(FoldNDelta(Normalize(e, normPlus), s, normPlus)) == Matches(e, s)
```

This is the bridge lemma that connects the generated matcher's postcondition back to the original source regex semantics.

## 7. The verified DFA compiler invariant

Open `compile.dfy`.

Find the datatype:

```dafny
datatype DFA = DFA(
  nStates: nat,
  start: nat,
  accepting: set<nat>,
  trans: map<(nat, char), nat>,
  ghost exprs: seq<Exp<char>>
)
```

This is the same idea as the generated file, but as a general compiler artifact. The runtime DFA has numeric states and a transition map. The ghost field `exprs` maps each state id to its residual regex meaning.

Find:

```dafny
ghost predicate DFACorrect(dfa: DFA, e: Exp<char>, alphabet: set<char>) {
  dfa.exprs[dfa.start] == NormalizeC(e)
  && forall st, c :: ... ==>
       dfa.exprs[dfa.trans[(st, c)]] == NDeltaC(dfa.exprs[st], c)
  && forall st :: ... ==>
       (st in dfa.accepting <==> Eps(dfa.exprs[st]))
}
```

This is the compiler invariant: start state means the normalized source expression; transitions preserve derivative meaning; accepting states agree with `Eps`.

Then find:

```dafny
lemma DFAAcceptsCorrect(dfa: DFA, e: Exp<char>, s: seq<char>, alphabet: set<char>)
  requires DFACorrect(dfa, e, alphabet)
  ensures DFAAccepts(dfa, s, alphabet) == Matches(e, s)
```

Any DFA satisfying that invariant accepts exactly the original regex language.

Finally, find `Compile`:

```dafny
method Compile(e: Exp<char>, alphabet: set<char>) returns (dfa: DFA)
  requires |alphabet| > 0
  decreases *
  ensures DFACorrect(dfa, e, alphabet)
```

The compiler explores reachable normalized derivatives by BFS and returns a DFA satisfying `DFACorrect`.

One caveat to be aware of:

> The current compiler uses `decreases *`; the returned DFA is proved correct, but the artifact does not yet prove total termination of BFS for all regexes. That would require a finiteness theorem for normalized derivatives.

## 8. Codegen

Open `codegen.dfy`.

Find the first part:

```dafny
method Codegen(e: Exp<char>, alphabet: set<char>) returns (code: string)
  requires |alphabet| > 0
  decreases *
{
  // BFS to discover states and transitions
  var startExpr := Normalize(e, NormPlus);
  var states := [startExpr];
  var stateOf := map[startExpr := 0];
  ...
}
```

Codegen repeats the derivative-state discovery, but instead of returning a DFA value, it prints a Dafny source file.

Then jump to the emitted proof snippets in `codegen.dfy`:

```dafny
lemma TransCorrect(...)
lemma AcceptCorrect(...)
lemma FoldTransCorrect(...)
lemma CorrectnessNDelta(...)
method MatchSpecialized(...)
```

The generator itself does not have to be trusted as a theorem. The emitted Dafny file (the `gen_star_ab_a.dfy` you started with) is checked independently. If the generator emits a wrong transition, `TransCorrect` fails.

## 9. Optional: run it

Open `test.dfy` or run `demo_star_ab_a.dfy`.

Expected examples for `(a|b)*a`:

```text
"a"    -> true
"ba"   -> true
"ab"   -> false
"abba" -> true
""     -> false
```

Use this if you want a concrete payoff at the end. The proof is the main event, not the printed booleans.

## 10. What to skip on a first pass

You can safely skip these while following the main thread:

- `parse.dfy`: useful convenience parser, but not part of the semantic theorem.
- `parse_test.dfy`: tests only.
- `minimize.dfy`: an interesting extra, but it distracts from the clean regex-to-DFA-to-codegen story.
- Full coalgebra diagrams: understand the idea, not the machinery.

## 11. Trust boundary / caveats

If you want to know precisely what is fully verified:

> The verified core starts from an `Exp<char>` AST and a finite alphabet. The artifact proves that derivative matching, normalized derivative folding, compiled DFA matching, and the generated specialized matcher agree with the regex semantics. The parser is a convenience layer, not a verified parser. The BFS/codegen methods use `decreases *`, so the current artifact proves correctness of returned/generated artifacts rather than total termination of compilation for all inputs.

## 12. One-minute version

If you're short on time, do only this:

1. Open `gen_star_ab_a.dfy`.
2. Read `TheExpr`, `S0`, `S1`, `Trans`, `Accept`.
3. Remember: runtime states are numbers; ghost meanings are residual regexes.
4. Read `TransCorrect` and `AcceptCorrect`.
5. Read the `MatchSpecialized` postcondition.
6. Open `bridge.dfy` and read `FoldNDeltaCorrect`.
7. Open `compile.dfy` and read `DFACorrect`.
8. Take away:

```text
The generated code is small.
The proof remembers why it is the same language.
```
