# Porting `Grammar/` and `Term/` to be generic in the theory

Measured, not estimated. Counts from the tree at the time of writing:
`Grammar/` is 157 files, of which **18 mention `_++_`**; `Term/` is 3
files, of which **0** do.

## Three buckets

### 1. Ports verbatim — the additive layer and all of `Term/`

`&`, `⊕`, `⊤`, `⊥`, `⇒`, `⊕ᴰ`, `&ᴰ`, `Lift`, `Maybe`, `Negation`,
`PropositionalTruncation`, `Equalizer`, `Limits`, `Subgrammar`,
`HLevels`, `Properties`, `Reify`, `Distributivity` — none of these ever
mentioned the monoid. They are pointwise in the index, so re-indexing
`String → Type` to `carrier s → Type` is the whole change.
`TheoryGrammar/Base.agda` and `TheoryGrammar/Rules.agda` carry them
across, with intro/elim and the universal property for each.

All of `Term/` is in this bucket. `Term/Base` (`id`, `_∘g_`, `isMono`,
`transportG`) is pure category structure on `_⊢_`; `Term/Nullary`
(`Element`, `ε⊢`) generalises to elements at any representable;
`Term/Category` builds the monoidal category, and only its *monoidal*
half needs bucket 2 — the underlying category is verbatim.

### 2. Has an analogue but changes shape — the 18 `++` files

These do not port one-to-one, because the thing they were generic over
(one binary `⊗`) becomes indexed by the operations of the theory.

| file | becomes |
|---|---|
| `LinearProduct/AsEquality/Base`, `AsPath/Base` | `⊗ˢ o` — **one per operation**, arity arbitrary |
| `LinearFunction/Base` | `⊸ᶠ o i` — **one per (operation, slot)**; `⟜`/`⊸` are slots `false`/`true` of `appop` |
| `LinearProduct/*/Properties` (assoc, unit) | instances of `eqn→Iso` — *derived from the theory's equations*, not hand-proved |
| `Epsilon/*` | `⊗ˢ o` at a nullary operation; the general case is `⌈ a ⌉` |
| `Literal/*` | `⌈ a ⌉`, representables |
| `Par/*` | one per operation, dual to `⊗ˢ` |
| `Derivative/*` | needs a *unary* operation to differentiate along; generic only for signatures that have one |
| `Later/InfixOrder`, `SuffixOrder` | needs a degree/grading homomorphism to ℕ, which not every theory has |
| `Yoneda/Reflect` | `⌈⌉-UP` — the Yoneda lemma for the substrate, already generic in `Rules.agda` |
| `SequentialUnambiguity/Properties`, `Greedy/Automata` | need equidivisibility (Levi's lemma); a genuine extra hypothesis |

The important structural change: **the assoc/unit isomorphisms stop
being theorems about strings and become instances of a single generic
theorem.** `TheoryGrammar/Equations.agda` proves that any equation of the
theory satisfied by the model induces an isomorphism of the two
composite connectives, with linearity of the equation as the exact side
condition.

### 3. Does not port — string-specific

`String/*`, `External/String/*`, `RegularExpression/*`, `Greedy/*`,
`Coinductive/*`. These are about a particular substrate. The
*replacements* are generic facts, per the brief:

- `⊤ ≅ String` is not an axiom about strings. It says the carrier is the
  **initial algebra of the shape functor** — every element is uniquely
  built from the operations. Generically: `⊤ ≅ μ(shape)` iff the model is
  free. (Stated; the fording needed to write `μ` without green slime is
  the remaining work, see below.)
- `split++`, `++-cancelˡEq` are consequences of **equidivisibility**,
  which is a property some theories have and others don't. They should be
  a named hypothesis, not ambient.

## The green slime, and why it is the same bug as the η failure

`String/Base.agda:29` has

```agda
Splitting w = Σ[ (w₁ , w₂) ] (w ≡ w₁ ++ w₂)
```

`_++_` is a *defined function* applied to bound variables, so this index
is neutral and unification is stuck — inversion needs `split++` instead
of a pattern match. That is the green slime, and it is the origin of the
`AsEquality` / `AsPath` duplication and of the ~45 lines of `Eq.ap` in
`Derivative/String.agda`.

It turns out to be the *same* defect that costs definitional η. Carrying
the proof `w ≡ w₁ ++ w₂` inside the convolution means the convolution is
a `Σ` one of whose components is `data` and therefore has no η. Both are
cured at once by indexing splittings **by the output** and exposing the
components as projections:

```agda
Split : (o) → carrier (resultSort o) → Type
parts : (o) (m) → Split o m → (a : arities o) → carrier (sortOf o a)
```

See `TheoryGrammar/Substrate.agda`. Recommendation for the existing
tree: change `Splitting` to the inductive family. Blast radius is the 18
files above; the payoff is that `AsPath` probably stops having a reason
to exist.

## Remaining work

- `μ` of the shape functor, forded so `resultSort o` is not a stuck
  index — then `⊤ ≅ μ(shape)` as the generic replacement for `⊤ ≅ String`.
- The `⊗ ⊣ ⊸` adjunction as a single `Iso`. Both sides now have
  definitional β/η *separately*; making them definitionally inverse to
  **each other** additionally requires the substrate's unfocused and
  focused splittings to be definitionally inverse. That holds for
  strings but is not automatic, and is the right place to state it as a
  substrate law.
- Port `Grammar/Inductive/` (μ, the SPFunctor) over `Substrate`; the
  `NO_POSITIVITY_CHECK` there is an opacity artefact, not slime, and the
  container presentation removes it.
