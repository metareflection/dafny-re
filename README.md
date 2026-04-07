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
4. **Verified matcher** — fold `Delta` over input, check `Eps`;
   proven correct against the denotational spec
5. **Expression normalization** — algebraic simplifications, proven
   to preserve semantics
6. **DFA compiler** — BFS over normalized derivatives produces a
   transition table; matching is O(n) with O(1) per character

No backtracking at any stage.

## Files

| File | Lines | What it does |
|------|-------|--------------|
| `re.dfy` | Core theory from the paper: `Exp`, `Lang`, `Denotational`, `Operational`, bisimilarity, algebra/coalgebra homomorphism proofs |
| `walk.dfy` | `Walk` (fold delta over a string), `Matches` spec, `MatchesEquivFoldDelta` |
| `match.dfy` | `Match` method — verified on-the-fly derivative matcher |
| `normalize.dfy` | `Normalize` with algebraic laws + `NormalizeCorrect` proof |
| `compile.dfy` | `Compile` (BFS to DFA) + `DFAMatch` (table-driven matcher) |
| `test.dfy` | Smoke tests for both matchers |

## Requirements

- [Dafny](https://github.com/dafny-lang/dafny) 4.x

## Verify

```sh
dafny verify re.dfy walk.dfy match.dfy normalize.dfy compile.dfy
```

Expected output: **78 verified, 0 errors**.

## Run

```sh
dafny run test.dfy --target cs --no-verify
```

Example output:
```
=== Derivative matcher ===
(a|b)*a  "a"    => true
(a|b)*a  "ba"   => true
(a|b)*a  "ab"   => false
(a|b)*a  "abba" => true
(a|b)*a  ""     => false

=== Compiled DFA ===
DFA states: 2
(a|b)*a  "a"    => true
(a|b)*a  "ba"   => true
(a|b)*a  "ab"   => false
(a|b)*a  "abba" => true
(a|b)*a  ""     => false

=== a(a|b) via DFA ===
DFA states: 4
a(a|b)  "ab" => true
a(a|b)  "ba" => false
a(a|b)  "aa" => true
a(a|b)  "a"  => false
```

## Verified vs unverified

The correctness chain that is fully machine-checked:

```
Match(e, s) == Matches(e, s)           -- match.dfy
Matches(e, s) == Eps(FoldDelta(e, s))  -- walk.dfy (MatchesEquivFoldDelta)
Bisimilar(Denotational(Normalize(e)),
          Denotational(e))             -- normalize.dfy (NormalizeCorrect)
```

What is *not* yet proven:
- BFS termination in `Compile` (uses `decreases *`)
- End-to-end `DFAAccepts(dfa, s) <==> Matches(e, s)`
- `Comp(e, One) = e` (Z3 timeout on the coinductive proof)
- `Star(Star(e)) = Star(e)`, full ACI of `Plus`

See [DESIGN.md](DESIGN.md) for details.
