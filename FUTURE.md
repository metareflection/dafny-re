# Future Work

## In Progress

### Algebraic Laws and BFS Termination (`feature/algebraic-laws-termination`)

Prove algebraic laws on `Languages.Lang` that strengthen the normalizer
and work toward removing `decreases *` from `Compile`.

- **`Comp(L, One()) ~ L`** (right identity). The left identity is done
  (`CompOneLeft` in `normalize.dfy`). The right identity has caused Z3
  timeouts on direct coinductive proofs; a prefix-level approach
  (`Bisimilar#[k]`) with manual unfolding is the likely path.
- **Commutativity of `Plus`**: `Plus(L1, L2) ~ Plus(L2, L1)`.
  Straightforward coinductively. Enables the normalizer to sort operands
  for better deduplication.
- **`Star(Star(e)) = Star(e)`**. Requires associativity of `Comp` on
  languages — a significant undertaking.
- **Full ACI of `Plus`**. Associativity + commutativity + idempotence
  would let the normalizer canonicalize sums, collapsing more derivative
  classes.

Once enough laws are in place, the goal is to prove that the set of
normalized derivatives of any expression is finite (Brzozowski's
theorem), which would establish BFS termination and eliminate
`decreases *`.

### Regex Parser (`feature/parser`)

A recursive descent parser from standard regex string syntax to
`Exp<char>`, desugaring syntactic sugar into the existing constructors:

- `a?` → `Plus(Char('a'), One)`
- `a+` → `Comp(Char('a'), Star(Char('a')))`
- `[abc]` → `Plus(Char('a'), Plus(Char('b'), Char('c')))`
- `.` → `Plus` over a provided alphabet
- Grouping, escape sequences, standard precedence

The parser itself does not need verification — correctness of matching
is guaranteed by the downstream verified pipeline regardless of what
expression the parser produces.

### DFA Minimization (`feature/dfa-minimization`)

Moore's algorithm for DFA state minimization, proven correct.

- Partition refinement: start with {accepting, non-accepting}, refine
  until stable.
- Build a quotient DFA whose states are equivalence classes.
- Prove the minimized DFA accepts the same language as the original.
- Termination is straightforward: the number of classes is bounded by
  `nStates` and strictly increases each round.

## Planned

### Extended Regex Features

Brzozowski derivatives extend naturally to:

- **Intersection** (`Inter(e1, e2)`): `Delta(Inter(e1, e2), a) = Inter(Delta(e1, a), Delta(e2, a))`, `Eps(Inter(e1, e2)) = Eps(e1) && Eps(e2)`
- **Complement** (`Not(e)`): `Delta(Not(e), a) = Not(Delta(e, a))`, `Eps(Not(e)) = !Eps(e)`

These stay within regular languages and the coalgebraic framework
carries through with modest effort.

### Decidability of Regex Equivalence

Compile two expressions to DFAs and check bisimilarity of start states.
The existing infrastructure (normalization, BFS, bisimilarity) provides
most of what's needed. This would give a verified decision procedure for
regular expression equivalence.

### Verified Compilation to External Targets

Emit C, Rust, or another target language from the DFA, with a proof that
the emitted code faithfully implements the transition table. This would
remove the need to trust the target language's compiler for the regex
matching logic.

### Complexity Bounds

Machine-check that the on-the-fly matcher runs in O(|s|) derivative
steps and that the compiled DFA runs in O(|s|) with O(1) per character
(given a fixed expression/DFA).
