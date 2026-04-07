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

The key operations for matching are already present:

| Operation | Type | Role |
|-----------|------|------|
| `Eps(e)` | `Exp -> bool` | Does `e` accept the empty word? |
| `Delta(e)(a)` | `Exp -> A -> Exp` | Derivative: next state after reading `a` |

Together they define an unpointed DFA whose states are expressions.

## Architecture

```
                   Denotational
        Exp --------------------------> Lang
         |                                ^
    Eps, |                                | (bisimilar)
   Delta |                                |
         v          match/compile         |
    DFA states -------- ... ----------> accept/reject
```

Three layers, built incrementally:

### Layer 1: On-the-fly matcher (derivative interpreter)

Walk the input string, applying `Delta` at each character. Check `Eps`
at the end. No precomputation, no backtracking.

```
method Match(e: Exp<char>, s: seq<char>) returns (accepts: bool)
  ensures accepts == Matches(e, s)
```

Where `Matches(e, s)` is a ghost predicate defined via `Denotational`:

```
ghost predicate Matches(e: Exp, s: seq<char>) {
  Walk(Denotational(e), s).eps
}
```

**Proof chain**: the imperative loop computes `Eps(FoldDelta(e, s))`,
which equals `Walk(Operational(e), s).eps` (by `OperationalWalkEps`),
which equals `Walk(Denotational(e), s).eps` (by `BisimilarWalkEps` +
`OperationalAndDenotationalAreBisimilar`), which is `Matches(e, s)`.

### Layer 2: Expression normalization

Brzozowski derivatives can produce expressions that grow without bound.
`Normalize` applies algebraic simplifications bottom-up:

- `Plus(e, Zero) = e`, `Plus(Zero, e) = e`, `Plus(e, e) = e`
- `Comp(Zero, e) = Zero`, `Comp(e, Zero) = Zero`, `Comp(One, e) = e`
- `Star(Zero) = One`, `Star(One) = One`

Each rule is proven to preserve the denotational semantics up to
bisimilarity, composed into the main theorem:

```
lemma NormalizeCorrect(e: Exp)
  ensures Bisimilar(Denotational(Normalize(e)), Denotational(e))
```

### Layer 3: Ahead-of-time DFA compilation

BFS from `Normalize(e)`, applying `Normalize(Delta(state)(a))` for each
character in the alphabet. Each unique normalized derivative becomes a
DFA state. The result is a transition table.

```
method Compile(e: Exp<char>, alphabet: set<char>) returns (dfa: DFA)
  ensures WellFormedDFA(dfa, alphabet)
```

Matching with the compiled DFA is a single table-driven loop:
O(|input|) time, O(1) per character.

BFS termination relies on finiteness of derivative classes
(Brzozowski's theorem). This is not proven in Dafny; the compiler
uses `decreases *`.

## Module Structure

```
re.dfy           -- Exp, Lang, Denotational, Operational, bisimilarity (from paper)
walk.dfy         -- Walk, FoldDelta, MatchesEquivFoldDelta
match.dfy        -- Match method (verified derivative interpreter)
normalize.dfy    -- Normalize, algebraic laws, NormalizeCorrect
compile.dfy      -- Compile (BFS -> DFA), DFAMatch
test.dfy         -- Smoke tests for both matchers
```

## What Is Proven

- `Match` returns exactly `Matches(e, s)` (denotational spec)
- `Normalize` preserves denotational semantics up to bisimilarity
- `Compile` produces a well-formed DFA (all transitions defined, states in range)
- `DFAMatch` follows the transition table correctly

## What Is Not Proven

- **BFS termination**: `Compile` uses `decreases *`. Proving finiteness
  of normalized derivative classes would require showing a bound on the
  number of distinct expressions reachable from a given starting expression.
- **DFA correctness**: no end-to-end proof that `DFAAccepts(dfa, s) <==> Matches(e, s)`.
  This would require connecting the BFS exploration to `FoldNDelta` and
  `NormalizeCorrect`.
- **Comp(e, One) = e**: Z3 times out on this coinductive proof due to
  lambda unfolding in the `Languages.Comp` codatatype definition.
- **Star(Star(e)) = Star(e)**: requires associativity of Comp, deferred.
- **ACI of Plus**: associativity, commutativity not implemented; only
  idempotence is proven.
