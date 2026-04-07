# Verified Regex Matching via Brzozowski Derivatives

## Goal

Build a verified, no-backtracking regular expression matcher in Dafny,
compiling down to a deterministic finite automaton (DFA). Every step
carries a machine-checked proof that the compiled matcher accepts
exactly the language denoted by the source expression.

## Foundation

`re.dfy` formalizes:

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
at the end. No precomputation, no backtracking. Linear in input length
per step (derivative size can grow, addressed in Layer 2).

```
method Match(e: Exp<char>, s: seq<char>) returns (accepts: bool)
  ensures accepts <==> Matches(e, s)
```

Where `Matches(e, s)` is a ghost predicate defined via `Denotational`:

```
ghost predicate Matches(e: Exp, s: seq<char>) {
  Denotational(e).Walk(s).eps
}

ghost function Walk(L: Lang, s: seq<A>): Lang {
  if |s| == 0 then L else Walk(L.delta(s[0]), s[1..])
}
```

**Proof obligation**: connect the imperative loop (folding `Delta` over
the input) to the coinductive `Walk` on `Operational(e)`, then use
`OperationalAndDenotationalAreBisimilar` to bridge to `Denotational`.

### Layer 2: Expression normalization

Brzozowski derivatives can produce expressions that grow without bound.
To guarantee termination of DFA construction (Layer 3) and bound
per-step cost of matching (Layer 1), normalize expressions modulo:

- **ACI** of `Plus` (associativity, commutativity, idempotence)
- **Identity/annihilator laws**: `Plus(e, Zero) = e`, `Comp(e, One) = e`,
  `Comp(e, Zero) = Zero`, `Star(Star(e)) = Star(e)`

Define a function `Normalize: Exp -> Exp` and prove:

```
lemma NormalizeCorrect(e: Exp)
  ensures Bisimilar(Denotational(Normalize(e)), Denotational(e))
```

With normalization, the set of reachable derivatives becomes finite for
any fixed expression — this is Brzozowski's theorem.

A canonical representation for `Plus` (sorted, flattened, deduplicated
list of summands) makes equality decidable, which is needed for state
deduplication in Layer 3.

### Layer 3: Ahead-of-time DFA compilation

Enumerate all reachable normalized derivatives from the start expression.
Each unique derivative becomes a DFA state. Build a transition table.

```
datatype DFA<A> = DFA(
  start: nat,
  accept: set<nat>,
  trans: map<(nat, A), nat>
)

method Compile(e: Exp<char>, alphabet: set<char>) returns (dfa: DFA<char>)
  ensures forall s :: DFAAccepts(dfa, s) <==> Matches(e, s)
```

**Exploration algorithm**: BFS/DFS from `Normalize(e)`, applying
`Normalize(Delta(state)(a))` for each `a` in the alphabet, collecting
states until fixpoint. Termination follows from finiteness of
normalized derivatives.

**Output**: a transition table indexed by `(state_id, char)`. This is
the "compiled DFA" — matching is a single table-driven loop with no
backtracking, O(|input|) time, O(1) per character.

## Proof Strategy

### Layer 1 correctness

1. Define `Walk` on `Lang` (fold `delta` over a string).
2. Show the imperative `Match` loop computes `Eps(fold Delta over s)`.
3. Show `Operational(e).Walk(s).eps == Eps(fold Delta e s)` by induction on `s`,
   using the definition of `Operational`.
4. Show `Denotational(e).Walk(s).eps == Operational(e).Walk(s).eps` by
   `OperationalAndDenotationalAreBisimilar` + a lemma that bisimilar
   languages agree on `Walk`.

### Layer 2 correctness

1. Prove each normalization rule preserves `Denotational` up to bisimilarity.
2. Compose into `NormalizeCorrect`.
3. Prove finiteness: the set `{ Normalize(Delta*(e)(w)) | w in A* }` is finite.
   This is the classical result; the Dafny proof would show a bound on the
   number of distinct normalized forms reachable from a given expression.

### Layer 3 correctness

1. Show the BFS exploration terminates (by finiteness from Layer 2).
2. Show the transition table faithfully represents the derivative relation.
3. Show the DFA accept set corresponds to `Eps`.
4. Compose: `DFAAccepts(dfa, s) <==> Matches(e, s)`.

## Module Structure

```
re.dfy                 -- existing: Exp, Lang, Denotational, Operational, bisimilarity
walk.dfy               -- Walk on Lang, connection lemmas
normalize.dfy          -- expression normalization, ACI laws, correctness
match.dfy              -- Layer 1: on-the-fly derivative matcher
compile.dfy            -- Layer 3: DFA compilation
```

## Implementation Order

1. **`walk.dfy`** — `Walk` function + lemma that bisimilar languages agree on Walk.
   Small, self-contained, unblocks everything else.

2. **`match.dfy`** — imperative `Match` method with loop invariant tying
   the accumulator to `Walk`. This is the first runnable, verified artifact.

3. **`normalize.dfy`** — expression normalization. Most proof effort lives here.
   Can be developed in parallel with using the unnormalized matcher.

4. **`compile.dfy`** — DFA construction. Depends on normalization for termination.
   The compiled DFA is a `map` or array; the matcher is a trivial loop over it.

## Open Questions

- **Alphabet representation**: `Delta` is parametric over `A`. For DFA
  construction, we need a finite alphabet. Pass it explicitly, or
  extract it from the expression?

- **Minimization**: Brzozowski's double-reversal minimization could
  produce a minimal DFA. Worth verifying, but not required for
  correctness.

- **Compilation target**: Dafny compiles to C#, Java, Go, Python, JS.
  The DFA transition table is a pure data structure — any target works.
  For performance-critical use, the compiled DFA could be emitted as
  a standalone state machine in the target language.

- **Submatch extraction**: Out of scope for now. Would require extending
  `Exp` with capture groups and tracking match boundaries through the
  derivative.
