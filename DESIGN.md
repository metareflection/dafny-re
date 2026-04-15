# Verified Regex Matching via Brzozowski Derivatives

## Goal

Build a verified, no-backtracking regular expression matcher in Dafny,
compiling down to a deterministic finite automaton (DFA). Every step
carries a machine-checked proof that the compiled matcher accepts
exactly the language denoted by the source expression.

## Foundation

`re.dfy` formalizes the coalgebraic semantics of regular expressions
from Zetzsche and Rozowski (arXiv:2409.09889v1):

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

Together they define an unpointed DFA whose states are expressions.

## Architecture

Three layers, each verified:

### Layer 1: On-the-fly matcher (derivative interpreter)

`match.dfy` — Fold `Delta` over input, check `Eps` at the end.

```
method Match(e: Exp<char>, s: seq<char>) returns (accepts: bool)
  ensures accepts == Matches(e, s)
```

**Proof chain**: imperative loop → `FoldDelta` → `Operational` →
`Denotational` via `OperationalAndDenotationalAreBisimilar`.

### Layer 2: Expression normalization

`normalize.dfy` — Apply algebraic simplifications bottom-up:

- `Plus(e, Zero) = e`, `Plus(Zero, e) = e`, `Plus(e, e) = e`
- `Comp(Zero, e) = Zero`, `Comp(e, Zero) = Zero`, `Comp(One, e) = e`
- `Star(Zero) = One`, `Star(One) = One`

```
lemma NormalizeCorrect(e: Exp)
  ensures Bisimilar(Denotational(Normalize(e)), Denotational(e))
```

### Layer 3: Verified DFA compiler

`compile.dfy` — BFS over normalized derivatives. Proven correct:

```
lemma DFAAcceptsCorrect(dfa, e, s, alphabet)
  requires DFACorrect(dfa, e, alphabet)
  ensures DFAAccepts(dfa, s, alphabet) == Matches(e, s)
```

The DFA invariant (`DFACorrect`) ensures:
- Start state maps to `Normalize(e)`
- Each transition `(st, c) -> tid` satisfies `exprs[tid] == NDelta(exprs[st], c)`
- Accepting states correspond to `Eps`

### Layer 4: Self-certifying codegen

`gen_star_ab_a.dfy` — Example of a generated specialized matcher.
The generated code:

1. Defines the DFA as pure functions (`Trans`, `Accept`, `FoldTrans`)
2. Proves each transition matches `NDelta` on ground terms
3. Proves `FoldTrans` tracks `FoldNDelta` by induction
4. Runs a simple state machine loop (no maps, no Exp types at runtime)
5. Carries `ensures accepts == Eps(FoldNDelta(Normalize(e), s))`

The bridge lemma `FoldNDeltaCorrect` (in `bridge.dfy`) connects this
to the denotational semantics: `Eps(FoldNDelta(Normalize(e), s)) == Matches(e, s)`.

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
              └── gen_star_ab_a.dfy
  parse.dfy (includes re.dfy)
```

## What Is Proven

- `Match` is correct against `Matches` (denotational spec)
- `Normalize` preserves semantics up to bisimilarity
- `Compile` produces a correct DFA (`DFAAccepts <==> Matches`)
- `DFAMatch` follows the transition table correctly
- Generated matchers are correct (`accepts == Eps(FoldNDelta(Normalize(e), s))`)
- The bridge connects all formulations: `FoldNDelta` ↔ `Matches` ↔ `FoldDelta`

## What Is Not Proven

- **BFS termination**: `Compile` uses `decreases *`
- **`Comp(e, One) = e`**: Z3 timeout on coinductive proof involving
  `Languages.Comp` lambda unfolding
- **`Star(Star(e)) = Star(e)`**: requires Comp associativity
- **ACI of Plus**: only idempotence proven
