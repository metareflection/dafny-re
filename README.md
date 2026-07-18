# dafny-re

Verified regular expression matching in [Dafny](https://dafny.org/),
built on the coalgebraic semantics of Brzozowski derivatives.

Based on: *Well-Behaved (Co)algebraic Semantics of Regular Expressions
in Dafny* by Stefan Zetzsche and Wojciech Rozowski
([arXiv:2409.09889](https://arxiv.org/abs/2409.09889)).

## Goal

Build a verified, no-backtracking regular expression matcher in Dafny,
compiling down to a deterministic finite automaton (DFA). Every step
carries a machine-checked proof that the compiled matcher accepts
exactly the language denoted by the source expression.

## Foundation

`re.dfy` formalizes the coalgebraic semantics of regular expressions:

- `Exp<A>` — regular expressions (inductive datatype)
- `Lang<!A>` — formal languages (coinductive codatatype)
- `Denotational: Exp -> Lang` — what an expression *means*
- `Operational: Exp -> Lang` — how an expression *runs* (via Brzozowski derivatives)
- `OperationalAndDenotationalAreBisimilar` — the two coincide up to bisimilarity

The key operations for matching:

| Operation | Type | Role |
|-----------|------|------|
| `Eps(e)` | `Exp -> bool` | Does `e` accept the empty word? |
| `Delta(e, a)` | `(Exp, A) -> Exp` | Derivative: next state after reading `a` |

Together they define a DFA whose states are expressions.

## Architecture

### Layer 1: On-the-fly matcher

`match.dfy` — Fold `Delta` over input, check `Eps` at the end.

```dafny
method Match(e: Exp<char>, s: seq<char>) returns (accepts: bool)
  ensures accepts == Matches(e, s)
```

Proof chain: imperative loop → `FoldDelta` → `Operational` →
`Denotational` via `OperationalAndDenotationalAreBisimilar`.

### Layer 2: Expression normalization

`normalize.dfy` — Algebraic simplifications bottom-up, proven to
preserve semantics:

- Identity/annihilator: `Plus(e, Zero) = e`, `Comp(Zero, e) = Zero`,
  `Comp(One, e) = e`, `Comp(e, One) = e`
- Idempotence: `Plus(e, e) = e`
- Full ACI of Plus: commutativity, associativity, sorted canonicalization
- Star absorption: `Star(Zero) = One`, `Star(One) = One`

```dafny
lemma NormalizeCorrect(e: Exp, normPlus: ...)
  requires NormPlusSpec(normPlus)
  ensures Bisimilar(Denotational(Normalize(e, normPlus)), Denotational(e))
```

The normalizer is parameterized by a Plus strategy: `NormPlus` (generic)
or `NormPlusChar` (full ACI with sorted operands for `Exp<char>`).

### Layer 3: Verified DFA compiler

`compile.dfy` — BFS over normalized derivatives.

```dafny
lemma DFAAcceptsCorrect(dfa, e, s, alphabet)
  requires DFACorrect(dfa, e, alphabet)
  ensures DFAAccepts(dfa, s, alphabet) == Matches(e, s)
```

### Layer 4: Verified DFA minimization

`minimize.dfy` — Moore's partition-refinement algorithm. The minimized
DFA carries a self-contained correctness guarantee:

```dafny
method Minimize(dfa: DFA, e: Exp<char>, alphabet: set<char>) returns (minDfa: DFA)
  requires DFACorrect(dfa, e, alphabet)
  ensures forall s :: ... ==> DFAAccepts(minDfa, s, alphabet) == Matches(e, s)
```

### Layer 5: Self-certifying codegen

`codegen.dfy` — Generates a standalone Dafny matcher from a regex.
The output (`gen_star_ab_a.dfy`) contains:

1. DFA as pure functions (`Trans`, `Accept`, `FoldTrans`)
2. Each transition proven to match `NDelta` on ground terms
3. `FoldTrans` proven to track `FoldNDelta` by induction
4. No maps, no `Exp` types, no codatatypes at runtime
5. `ensures accepts == Eps(FoldNDelta(Normalize(TheExpr()), s))`

For the full regex spec `accepts == Matches(TheExpr(), s)`, compose with
`FoldNDeltaCorrect` (`bridge.dfy`) at the use site:

```dafny
accepts := MatchSpecialized(s);
NormPlusSatisfiesSpec<char>();
FoldNDeltaCorrect(TheExpr(), s, NormPlus);   // now: accepts == Matches(TheExpr(), s)
```

The generated file is verbatim `Codegen` output — do not edit it by hand;
regenerate it (see `run_gen_star_ab_a.dfy`). The runnable demo lives separately
in `demo_star_ab_a.dfy` so the generated artifact stays pure.

### Parser

`parse.dfy` — Recursive descent parser from standard regex syntax to
`Exp<char>`. Supports literals, `|`, concatenation, `*`, `+`, `?`,
grouping, character classes, and escape sequences. The parser is
unverified — correctness of matching is guaranteed by the downstream
verified pipeline regardless of what expression the parser produces.

## Files

| File | What |
|------|------|
| `re.dfy` | Core theory: `Exp`, `Lang`, `Denotational`, `Operational`, bisimilarity, homomorphism proofs |
| `walk.dfy` | `Walk`, `FoldDelta`, `Matches` spec, `MatchesEquivFoldDelta` |
| `match.dfy` | `Match` — verified on-the-fly derivative interpreter |
| `normalize.dfy` | `Normalize` with algebraic laws (full ACI of Plus, Comp identities) + `NormalizeCorrect` |
| `bridge.dfy` | `FoldNDeltaCorrect` — connects normalized derivative fold to `Matches` |
| `compile.dfy` | `Compile` (BFS to DFA) + `DFAMatch` — both proven correct |
| `minimize.dfy` | `Minimize` (Moore's algorithm) — verified DFA minimization |
| `parse.dfy` | Recursive descent regex parser: standard syntax → `Exp<char>` |
| `parse_test.dfy` | 38 test cases for the parser |
| `codegen.dfy` | `Codegen` — generates a self-certifying Dafny matcher from a regex |
| `run_gen_star_ab_a.dfy` | Runner that (re)generates `gen_star_ab_a.dfy` for `(a\|b)*a` |
| `gen_star_ab_a.dfy` | Verbatim `Codegen` output for `(a\|b)*a` — 2-state DFA, proves `accepts == Eps(FoldNDelta(...))` |
| `demo_star_ab_a.dfy` | Runnable demo exercising `gen_star_ab_a.dfy` |
| `test.dfy` | Smoke tests |

## Module Dependency Graph

```
re.dfy
  ├── walk.dfy
  │     └── match.dfy
  └── normalize.dfy
        └── bridge.dfy
              ├── compile.dfy
              │     └── minimize.dfy
              ├── codegen.dfy
              │     └── run_gen_star_ab_a.dfy  (regenerates ↓)
              └── gen_star_ab_a.dfy
                    └── demo_star_ab_a.dfy
  parse.dfy (includes re.dfy)
```

## Requirements

[Dafny](https://github.com/dafny-lang/dafny) 4.x

## Verify

```sh
dafny verify re.dfy walk.dfy match.dfy normalize.dfy bridge.dfy compile.dfy minimize.dfy parse.dfy codegen.dfy gen_star_ab_a.dfy
```

## Run

```sh
# On-the-fly derivative matcher + verified DFA
dafny run test.dfy --target cs --no-verify

# Self-certifying specialized matcher for (a|b)*a (demo of the generated file)
dafny run demo_star_ab_a.dfy

# Parser tests
dafny run parse_test.dfy --target cs --no-verify
```

## What is proven

The complete verified chain:

```
MatchSpecialized(s)
  == Eps(FoldNDelta(Normalize(e), s))     gen_star_ab_a.dfy
  == Matches(e, s)                        bridge.dfy  (FoldNDeltaCorrect, composed at use site)
  == Eps(FoldDelta(e, s))                 walk.dfy    (MatchesEquivFoldDelta)
  == Match(e, s)                          match.dfy

DFAMatch(Compile(e, alpha), e, s, alpha)
  == DFAAccepts(dfa, s, alpha)            compile.dfy (DFAMatch spec)
  == Matches(e, s)                        compile.dfy (DFAAcceptsCorrect)

DFAAccepts(Minimize(dfa, e, alpha), s, alpha)
  == Matches(e, s)                        minimize.dfy (Minimize ensures)
```

Every arrow is a machine-checked Dafny proof.

Additionally:

- `Match` is correct against `Matches` (denotational spec)
- `Normalize` preserves semantics up to bisimilarity, for any `normPlus` satisfying `NormPlusSpec`
- Full ACI of `Plus` on languages: commutativity, associativity, idempotence
- `Comp(L, One()) ~ L` and `Comp(One(), L) ~ L` (both identity laws)
- `Compile` produces a correct DFA (`DFAAccepts <==> Matches`)
- `Minimize` produces a correct minimized DFA (`DFAAccepts <==> Matches`)
- Generated matchers prove `accepts == Eps(FoldNDelta(Normalize(e), s))`; composing with `FoldNDeltaCorrect` at the use site gives the full regex spec (`accepts == Matches(e, s)`)
- The bridge connects all formulations: `FoldNDelta` ↔ `Matches` ↔ `FoldDelta`
- The parser is unverified (convenience layer; correctness guaranteed by the downstream pipeline)

## Codegen

`Codegen` takes a regex and alphabet at runtime, runs BFS over
normalized derivatives, and prints a complete Dafny source file.
The output is a self-certifying matcher — Dafny verifies it
independently, with no trust required in the generator.

`run_gen_star_ab_a.dfy` is the committed runner for `(a|b)*a`. Build the
native binary and run it for clean stdout (no verifier banner to strip), then
check the artifact verifies independently:

```sh
dafny build --no-verify run_gen_star_ab_a.dfy && ./run_gen_star_ab_a > gen_star_ab_a.dfy
dafny verify gen_star_ab_a.dfy
```

For a different regex, copy `run_gen_star_ab_a.dfy`, swap the `Codegen(...)`
call, and repeat.

## What is not proven

- **BFS termination** in `Compile` (uses `decreases *`). Proving
  finiteness of derivative classes requires formalizing Brzozowski's
  theorem.
- **`Star(Star(e)) = Star(e)`** — requires `Comp` associativity on
  languages.
- **Moore refinement termination** in `Minimize` (uses `decreases *`).
  Bounded by `nStates` iterations but not yet formalized.
