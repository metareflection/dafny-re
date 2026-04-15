# dafny-re vs RE2: Architecture Comparison

## Shared Philosophy

Both projects reject backtracking. Both guarantee linear-time matching
by using automata theory. Both compile regular expressions into
deterministic finite automata. The difference is in how they get there
and what guarantees they provide.

## The Two Routes to a DFA

### RE2: NFA → Powerset Construction (Lazy)

RE2 follows the classical textbook pipeline:

1. Parse regex string → `Regexp` AST
2. Simplify the AST (rewrite `a{3}` into `aaa`, etc.)
3. Compile to a Thompson NFA (`Prog` — a bytecode program)
4. During matching, lazily determinize via the powerset construction

Each DFA state in RE2 is a set of NFA instruction pointers. States are
computed on demand: the first time byte `c` is seen in state `s`,
RE2 computes the set of NFA states reachable via `c` and caches the
result. If memory runs out, the cache is flushed.

### dafny-re: Brzozowski Derivatives (Direct)

dafny-re skips the NFA entirely:

1. Define `Exp` (the regex AST) with `Eps` and `Delta` — this gives
   expressions the structure of a (possibly infinite-state) DFA directly
2. Normalize derivatives to collapse equivalent states
3. BFS over normalized derivatives to enumerate all reachable states
4. Emit the transition table

Each DFA state is a normalized expression. The expression *is* the
automaton state — `Delta(e, a)` is the transition function, `Eps(e)` is
the acceptance predicate. This is the coalgebraic view: `(Eps, Delta)`
makes `Exp` a coalgebra, which is precisely a deterministic automaton.

Both approaches produce DFAs that accept the same language. The states
are just represented differently: sets of NFA states vs. normalized
expressions.

## Matching Strategies

dafny-re provides three matching strategies at different points on the
eager/lazy spectrum:

| Strategy | Upfront Cost | Per-Match Cost | Caching |
|----------|-------------|----------------|---------|
| `Match` (on-the-fly) | None | Recomputes derivatives each time | None |
| Lazy DFA (not yet implemented) | None | Computes + caches on demand | Yes |
| `Compile` + `DFAMatch` | Full BFS | Table lookup only | Full DFA |
| `Codegen` output | Full BFS + verification | Inlined branches | Baked in |

RE2 operates primarily in the lazy DFA mode, with an NFA fallback for
submatch extraction.

`Match` is analogous to RE2's inline usage where the regex is recompiled
on each call. `Compile` + `DFAMatch` is analogous to RE2's precompiled
`RE2` object that is reused across calls:

```dafny
// dafny-re: compile once, match many
var dfa := Compile(expr, alpha);
var r1 := DFAMatch(dfa, expr, "a", alpha);
var r2 := DFAMatch(dfa, expr, "ba", alpha);
```

```cpp
// RE2: compile once, match many
RE2 re("(a|b)*a");
RE2::FullMatch("a", re);
RE2::FullMatch("ba", re);
```

Note: `DFAMatch` takes both `dfa` and `expr` because the postcondition
`ensures accepts == Matches(e, s)` needs the expression to state
correctness. The `expr` parameter is only used in the spec — at runtime,
only the DFA's transition table is consulted. This could be cleaned up
with a wrapper type:

```dafny
datatype CompiledRegex = CompiledRegex(
  dfa: DFA,
  ghost expr: Exp<char>,
  alphabet: set<char>
)
```

## The DFAs Can Differ

For the same regex, the Brzozowski DFA and the powerset DFA can have
different numbers of states. Neither is guaranteed to produce the minimal
DFA.

- The powerset DFA's size depends on the NFA construction (Thompson's
  gives O(n) NFA states, so at most 2^O(n) DFA states, though far fewer
  are typically reachable).
- The Brzozowski DFA's size depends on how many syntactically distinct
  normalized derivatives exist. More algebraic laws in the normalizer
  means fewer states.

Both can be minimized after construction (e.g., via Moore's algorithm)
to obtain the unique minimal DFA.

## Verification

This is the fundamental difference. RE2 has no formal verification. Its
correctness rests on the well-understood theory of Thompson's
construction and the powerset construction, plus extensive testing and
years of production use at Google.

dafny-re provides machine-checked proofs at every layer:

```
Matches(e, s)                          (denotational spec)
  == Eps(FoldDelta(e, s))              (walk.dfy: MatchesEquivFoldDelta)
  == Match(e, s)                       (match.dfy: loop correctness)

Matches(e, s)
  == Eps(FoldNDelta(Normalize(e), s))  (bridge.dfy: FoldNDeltaCorrect)
  == DFAAccepts(Compile(e), s)         (compile.dfy: DFAAcceptsCorrect)
  == MatchSpecialized(s)               (gen_*.dfy: self-certifying)
```

The bisimilarity result from the original paper
(`OperationalAndDenotationalAreBisimilar`) is the linchpin: it justifies
computing with `Delta`/`Eps` (operational) while stating correctness in
terms of `Denotational` (the language semantics).

## Feature Comparison

| Feature | RE2 | dafny-re |
|---------|-----|----------|
| Formal verification | No | Yes, machine-checked |
| Backreferences | No (by design) | No (not regular) |
| Character classes | Yes (`[a-z]`, `\d`, etc.) | Via parser desugaring (in progress) |
| Anchors (`^`, `$`) | Yes | Not yet |
| Submatch extraction | Yes (via NFA) | No |
| Lazy DFA | Yes | Not yet (could be added) |
| Eager DFA compilation | No | Yes (`Compile`) |
| DFA minimization | No | In progress (Moore's) |
| Codegen | No | Yes (self-certifying Dafny output) |
| Intersection/complement | No | Natural extension of derivatives |
| Guaranteed linear time | Yes | Yes (proven) |

## Why Derivatives Are Better for Verification

The Brzozowski derivative approach keeps everything in the expression
algebra, where bisimilarity, congruence, and normalization are
first-class concepts with rich proof infrastructure. The NFA powerset
construction would be much harder to verify because you'd need to reason
about sets of NFA states and their relationship to the language
semantics.

The coalgebraic framework provides a clean separation: `Denotational`
says what an expression means, `Operational` (via `Eps`/`Delta`) says
how to compute with it, and bisimilarity proves they agree. Every
subsequent layer — normalization, DFA compilation, codegen — plugs into
this framework through the same bisimilarity machinery.

## Self-Certifying Codegen

dafny-re's codegen produces standalone Dafny files that carry their own
correctness proofs. The generated code contains:

- `Trans(state, c)` — inlined DFA transitions (pure function on nats)
- `MatchSpecialized(s)` — the matcher
- `TransCorrect` — each transition matches `NDelta` (verified on ground terms)
- `FoldTransCorrect` — the fold tracks `FoldNDelta` (by induction)

The generator itself (`Codegen`) is unverified — it's just string
manipulation. But the output is independently verified by Dafny. If the
generator has a bug, the output fails to verify. This is the
proof-carrying code model: don't trust the compiler, trust the checker.

RE2 has no equivalent — its compiled form is trusted to be correct based
on the implementation, not independently checked.

## What dafny-re Could Adopt from RE2

The main idea worth considering is lazy DFA construction: compute
`NDelta` on demand during matching and cache the results, rather than
doing full BFS upfront. This would sidestep the BFS termination question
for the matching use case while still being provably correct via
`FoldNDeltaCorrect`. It would be a middle ground between `Match`
(no caching) and `Compile` (full eager construction).

Beyond that, RE2's richer syntax (character classes, repetition counts,
etc.) is already handled by desugaring into the existing `Exp` grammar —
the parser branch covers this.

The core architectural choice — derivatives on expressions rather than
powerset construction on NFA states — is the right one for a verified
pipeline and should not change.
