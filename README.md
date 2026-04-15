# dafny-re

Verified regular expression matching in [Dafny](https://dafny.org/),
built on the coalgebraic semantics of Brzozowski derivatives.

Based on: *Well-Behaved (Co)algebraic Semantics of Regular Expressions
in Dafny* by Stefan Zetzsche and Wojciech Rozowski
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
5. **Expression normalization** — algebraic simplifications (identity,
   annihilator, idempotence, full ACI of Plus, right identity of Comp),
   proven to preserve semantics
6. **Verified DFA compiler** — BFS over normalized derivatives produces a
   transition table, proven to accept exactly `Matches(e, s)`
7. **Verified DFA minimization** — Moore's partition-refinement algorithm,
   proven to preserve the accepted language
8. **Self-certifying codegen** — emit a specialized Dafny matcher with
   no maps or expression types at runtime, carrying its own correctness proof
9. **Regex parser** — recursive descent parser from standard regex syntax
   to `Exp<char>`, with desugaring of `+`, `?`, character classes, etc.

No backtracking at any stage.

## Files

| File | What |
|------|------|
| `re.dfy` | Core theory: `Exp`, `Lang`, `Denotational`, `Operational`, bisimilarity, homomorphism proofs |
| `walk.dfy` | `Walk`, `FoldDelta`, `Matches` spec, `MatchesEquivFoldDelta` |
| `match.dfy` | `Match` — verified on-the-fly derivative interpreter |
| `normalize.dfy` | `Normalize` with algebraic laws (incl. full ACI of Plus, right identity of Comp) + `NormalizeCorrect` |
| `bridge.dfy` | `FoldNDeltaCorrect` — connects normalized derivative fold to `Matches` |
| `compile.dfy` | `Compile` (BFS to DFA) + `DFAMatch` — both proven correct |
| `minimize.dfy` | `Minimize` (Moore's algorithm) — verified DFA minimization, proven to preserve `Matches` |
| `parse.dfy` | Recursive descent regex parser: standard syntax → `Exp<char>` |
| `parse_test.dfy` | 38 test cases for the parser |
| `codegen.dfy` | `Codegen` — generates a self-certifying Dafny matcher from a regex |
| `gen_star_ab_a.dfy` | Example output of `Codegen` for `(a\|b)*a` — 2-state DFA, self-certifying |
| `test.dfy` | Smoke tests |

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

DFAAccepts(Minimize(dfa, e, alpha), s, alpha)
  == Matches(e, s)                        minimize.dfy (Minimize ensures)
```

Every arrow is a machine-checked Dafny proof. The generated matcher
(`gen_star_ab_a.dfy`) has no maps, no expression types, no codatatypes
at runtime — just integer state transitions verified against the
denotational semantics.

## Parser

`parse.dfy` provides a recursive descent parser from standard regex
string syntax to `Exp<char>`:

```sh
# Parse and match in one shot
dafny run parse_test.dfy --target cs --no-verify
```

Supported syntax: literals, `|` (alternation), concatenation, `*`, `+`,
`?`, grouping with `()`, character classes `[abc]`, and escape sequences.
Standard precedence: postfix binds tightest, then concatenation, then `|`.

The parser is unverified — it's a convenience layer. Correctness of
matching is guaranteed by the downstream verified pipeline regardless
of what expression the parser produces.

## Codegen

`Codegen` takes a regex and alphabet at runtime, runs BFS over
normalized derivatives, and prints a complete Dafny source file.
The output is a self-certifying matcher — Dafny verifies it
independently, with no trust required in the generator.

```sh
# Write a codegen driver
cat > my_codegen.dfy << 'EOF'
include "codegen.dfy"
method Main() decreases * {
  var code := Codegen(Comp(Star(Plus(Char('a'), Char('b'))), Char('a')), {'a', 'b'});
  print code;
}
EOF

# Generate and save
dafny run my_codegen.dfy --target cs --no-verify > gen_my_matcher.dfy

# Verify the generated code (no trust in the generator!)
dafny verify gen_my_matcher.dfy
```

The generated file contains:
- `Trans(state, c)` — inlined DFA transitions (pure function on nats)
- `MatchSpecialized(s)` — the matcher, with `ensures accepts == Eps(FoldNDelta(Normalize(TheExpr()), s))`
- Transition correctness lemmas verified by Z3 on ground terms
- `FoldTransCorrect` — proof that `Trans` tracks normalized derivatives
- No maps, no `Exp` types, no codatatypes at runtime

## What is not proven

- **BFS termination** in `Compile` (uses `decreases *`). Proving
  finiteness of derivative classes requires formalizing Brzozowski's
  theorem.
- **`Star(Star(e)) = Star(e)`** — requires `Comp` associativity on
  languages.
- **Moore refinement termination** in `Minimize` (uses `decreases *`).
  Bounded by `nStates` iterations but not yet formalized.
