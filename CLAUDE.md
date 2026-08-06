# Working in this repository

## The phase distinction (read this before writing any term)

There are two phases, and code belongs to exactly one of them.

**Phase 1 — building the language.** Defining connectives, their intro
and elim rules, universal properties, and the *primitives* of a
substrate. Here you may pattern-match on the carrier, destructure
splittings, and write pointful Agda. This is where the abstraction
barrier is constructed.

**Phase 2 — using the language.** Every program, algorithm, parser,
sorter, or example. Here you may **only** compose `⊢`-combinators.

```
a program in the calculus is a term  A ⊢ B,
built ONLY from combinators and clearly-marked primitives
```

Concretely, in phase 2 you must not:

- pattern-match on the carrier (`[]` / `_∷_`, `Bool`, a splitting)
- write `f w x = …` with a visible index `w` and payload `x`
- use metalanguage `Dec`, `Maybe`, `List`, or `if_then_else_` where a
  connective exists (`MaybeG`, `⊕`, `⊕ᴰ`, `Dec⟨_⟩`)
- eliminate a sum by `with` or by matching `inl`/`inr` — use `⊕-E`,
  `⊕ᴰ-E`, `MaybeG-E`

Instead: `_∘g_`, `idg`, `⊕-I₁`, `⊕-I₂`, `⊕-E`, `⊕ᴰ-in`, `⊕ᴰ-E`, `&-I`,
`⊗ˢ-I`, `⊗ˢ-E`, `⌈⌉-E`, `löb`, `hyloC`. The full set is
`TheoryGrammar.RulesSub` (`RulesS`), which every instance should
re-export from its `Base`.

**If a phase-2 program needs something pointful, that is a signal you
are missing a primitive.** Name it, give it a `⊢` type, prove it once in
phase 1 with a comment saying it is a primitive, and then use it. Do not
inline the pointful reasoning into the program.

Worked example of the boundary: `Instances/Bags/Quicksort.agda` has
exactly two primitives — `bagCase` (decomposition) and `splitAround`
(partition, the only place the ordering is used) — and the coalgebra is
a composite of them with `⊕-E` / `⊕ᴰ-E` / `⊗-mk`.

### Why this matters, not just stylistically

Working internally *discharges proof obligations for free*. `_⊢_`
preserves the index and `⊗ˢ` splits it, so a term

```agda
merge : Sorted ⊗ Sorted ⊢ Sorted
```

is automatically permutation-correct — it cannot invent or drop
elements, because the index is the bag. Written as `Bag → Bag → Bag`
that same fact needs a separate hand-proof. Every escape into pointful
Agda is an obligation you have taken back on.

## Known traps

- **Grammar-valued implicits are not inferrable.** `MaybeG A w` unfolds
  to `A w ⊎ Unit*`, and `?A w` cannot be recovered from that. Take the
  grammar *explicitly* in any combinator over a derived connective.
- **Arities have no η.** An n-ary operation is a family over the arity
  (e.g. `Bool`), and `λ a → f a` is not definitionally `f`. This costs
  `⟜UMP`'s η, blocks implicit inference on `⊗I`, and is why
  `toC ∘ fromC` is not definitionally the identity.
- **Do not carry proofs in a `Split`.** `Substrate`'s splittings are
  data indexed by the output, with components as projections. Adding an
  equation component costs definitional η and reintroduces green slime.

## Build

```
cd src && agda --no-libraries --library-file=$HOME/.agda/libraries <file>
```
