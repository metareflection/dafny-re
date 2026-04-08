# dafny-re

Verified regular expression matching in [Dafny](https://dafny.org/),
built on the coalgebraic semantics of Brzozowski derivatives.

Based on: *Well-Behaved (Co)algebraic Semantics of Regular Expressions
in Dafny* by S. Zetzsche and W. Rozowski
([arXiv:2409.09889](https://arxiv.org/abs/2409.09889)).

## What this is

A machine-checked pipeline from regular expressions to deterministic
finite automata:

1. **Denotational semantics** — what a regex means (formal languages as
   a coinductive codatatype)
2. **Operational semantics** — Brzozowski derivatives (`Eps`, `Delta`)
3. **Bisimilarity proof** — the two semantics coincide
4. **Verified interpreter** — fold `Delta` over input, check `Eps`;
   proven correct against the denotational spec
5. **Expression normalization** — algebraic simplifications, proven
   to preserve semantics
6. **Verified DFA compiler** — BFS over normalized derivatives produces a
   transition table, proven to accept exactly `Matches(e, s)`
7. **Self-certifying codegen** — emit a specialized Dafny matcher with
   no maps or expression types at runtime, carrying its own correctness proof

No backtracking at any stage.

## Files

| File | What |
|------|------|
| `re.dfy` | Core theory: `Exp`, `Lang`, `Denotational`, `Operational`, bisimilarity, homomorphism proofs |
| `walk.dfy` | `Walk`, `FoldDelta`, `Matches` spec, `MatchesEquivFoldDelta` |
| `match.dfy` | `Match` — verified on-the-fly derivative interpreter |
| `normalize.dfy` | `Normalize` with algebraic laws + `NormalizeCorrect` |
| `bridge.dfy` | `FoldNDeltaCorrect` — connects normalized derivative fold to `Matches` |
| `compile.dfy` | `Compile` (BFS to DFA) + `DFAMatch` — both proven correct |
| `gen_star_ab_a.dfy` | Example generated matcher for `(a\|b)*a` — 2-state DFA, self-certifying |
| `test.dfy` | Smoke tests |

## Requirements

[Dafny](https://github.com/dafny-lang/dafny) 4.x

## Verify

```sh
dafny verify re.dfy walk.dfy match.dfy normalize.dfy bridge.dfy compile.dfy gen_star_ab_a.dfy
```

Expected: **111 verified, 0 errors**.

## Run

```sh
# On-the-fly derivative matcher + verified DFA
dafny run test.dfy --target cs --no-verify

# Self-certifying specialized matcher for (a|b)*a
dafny run gen_star_ab_a.dfy --target cs --no-verify
```

## What is proven

The complete verified chain:

```
MatchSpecialized(s)
  == Eps(FoldNDelta(Normalize(e), s))     gen_star_ab_a.dfy
  == Matches(e, s)                        bridge.dfy  (FoldNDeltaCorrect)
  == Eps(FoldDelta(e, s))                 walk.dfy    (MatchesEquivFoldDelta)
  == Match(e, s)                          match.dfy

DFAMatch(Compile(e, alpha), e, s, alpha)
  == DFAAccepts(dfa, s, alpha)            compile.dfy (DFAMatch spec)
  == Matches(e, s)                        compile.dfy (DFAAcceptsCorrect)
```

Every arrow is a machine-checked Dafny proof. The generated matcher
(`gen_star_ab_a.dfy`) has no maps, no expression types, no codatatypes
at runtime — just integer state transitions verified against the
denotational semantics.

## What is not proven

- **BFS termination** in `Compile` (uses `decreases *`). Proving
  finiteness of derivative classes requires formalizing Brzozowski's
  theorem.
- **`Comp(e, One) = e`** — Z3 timeout on the coinductive proof.
- **`Star(Star(e)) = Star(e)`**, full ACI of `Plus`.
