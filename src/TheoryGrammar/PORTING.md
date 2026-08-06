# Porting `Grammar/` to be generic in the theory

File-by-file, measured. `Grammar/` is **157 files**.

| axis | count | share |
|---|---|---|
| mention `⊗` | **57** | 36% |
| purely additive (no `⊗` anywhere) | **100** | 64% |
| import `Grammar.String` directly | 21 | 13% |
| mention `Splitting` | 13 | 8% |
| mention `Nullable` | 8 | 5% |

**Correction to the first pass of this audit.** It reported "18 files use
`_++_`" and treated that as the porting cost. That was the wrong axis:
`++` only catches files doing splitting *arithmetic*, not files that
merely *use* the tensor. The real number is **57**, and `LinearProduct/`
itself does not appear in the `++` count because it defines `⊗` rather
than reasoning about lengths. So the multiplicative surface is three
times larger than first reported — though still a minority of the tree.

`Term/` is 3 files, none of which mention `⊗` or `++`; it ports whole.

## Three buckets

### 1. Ports verbatim — the additive layer and all of `Term/` (100 files)

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

### 2. Has an analogue but changes shape — the 57 `⊗` files

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
| `Yoneda/Reflect` | `⌈⌉-UP` — the Yoneda lemma for the promodel, already generic in `Rules.agda` |
| `SequentialUnambiguity/Properties`, `Greedy/Automata` | need equidivisibility (Levi's lemma); a genuine extra hypothesis |

The important structural change: **the assoc/unit isomorphisms stop
being theorems about strings and become instances of a single generic
theorem.** `TheoryGrammar/Equations.agda` proves that any equation of the
theory satisfied by the model induces an isomorphism of the two
composite connectives, with linearity of the equation as the exact side
condition.

### 3. Does not port — string-specific

`String/*`, `External/String/*`, `RegularExpression/*`, `Greedy/*`,
`Coinductive/*`. These are about a particular promodel. The
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

See `TheoryGrammar/Fibered.agda`. Recommendation for the existing
tree: change `Splitting` to the inductive family. Blast radius is the 18
files above; the payoff is that `AsPath` probably stops having a reason
to exist.

## Remaining work

- `μ` of the shape functor, forded so `resultSort o` is not a stuck
  index — then `⊤ ≅ μ(shape)` as the generic replacement for `⊤ ≅ String`.
- The `⊗ ⊣ ⊸` adjunction as a single `Iso`. Both sides now have
  definitional β/η *separately*; making them definitionally inverse to
  **each other** additionally requires the promodel's unfocused and
  focused splittings to be definitionally inverse. That holds for
  strings but is not automatic, and is the right place to state it as a
  promodel law.
- Port `Grammar/Inductive/` (μ, the SPFunctor) over `Fibered`; the
  `NO_POSITIVITY_CHECK` there is an opacity artefact, not slime, and the
  container presentation removes it.

## Coverage: what `TheoryGrammar/` already has

Not a plan — a measurement against the 21 modules currently in
`TheoryGrammar/`.

| `Grammar/` group | files | covered by | state |
|---|---|---|---|
| Sum, Product, Top, Bottom, Lift, Maybe, Negation, PropTrunc, Equalizer, Limits, HLevels, Properties, Function, Equivalence | ~60 | `Rules`, `RulesFib` | **done** |
| Distributivity | 1 | `Distributive` | **done** |
| LinearProduct | 6 | `Fibered` (`⊗ˢ`) | **done** |
| LinearFunction | 2 | `Fibered` (`⊸ᶠ`), `CanonicalFocus` | **done** |
| Epsilon, Literal | 13 | `Representable` | **done** |
| Inductive, KleeneStar | 11 | `Inductive` (generic `μ`) | **done** |
| Par | 2 | `Par` (`Allˢ`) | **done** |
| SemanticAction | 2 | `SemanticAction` | **done** |
| Yoneda | 2 | `Representable` (`⌈⌉-UP`) | **done** |
| Later | 7 | `Graded` (`▷`, `löb`, `hyloC`) | **partial** — `Box`, `Infix` not ported |
| Subgrammar | 2 | — | **not started**, but additive; should be easy |
| Derivative | 3 | `Derivative` (`δ`, `DerivTensor`) | **done** |
| **SequentialUnambiguity** | 5 | — | **not started**; needs Levi |
| **Greedy** | 2 | — | **not started**; needs Levi |
| **RegularExpression** | 2 | — | **not started**; needs Derivative first |
| **Coinductive** | 4 | — | **not started**; no `ν` in the generic layer |
| String, External | 12 | — | *replaced*, not ported |

So the additive half is done, the multiplicative core is done, and what
remains is **18 files in five groups**, each blocked on one identifiable
hypothesis rather than on volume.

## The remaining work, in dependency order

1. ~~**`Derivative`**~~ — **done**. The correction to this entry is
   worth keeping: it does *not* need a unary operation. The derivative
   is **precomposition along a map of carriers**, and the maps worth
   using come from pinning all-but-one slot of an operation — which is
   already `Assembly` (`CanonicalFocus`). So `δ` exists for any theory,
   once per (operation, slot, choice of the rest). Every additive law
   (`⊤ ⊥ & ⊕ ⇒ ⊕ᴰ &ᴰ`) is `refl`, because the additive connectives are
   pointwise in the index and precomposition is what commutes with
   pointwise structure.

   What is genuinely non-generic is the ⊗ law, which must decide which
   slot absorbed the action — equidivisibility. It is `DerivTensor`, an
   inversion principle for `Split o (act x)`, discharged for strings by
   **pattern-matching `Split3`**: four lines, and `split++` never
   appears. That is the payoff the inductive-`Split` refactor was
   predicted to have, now measured.

   `strDecTensorδ` is the third `⊗-EM` constructor, and reaches the
   same `DecTensorRule` that `Strings/Decidable` reaches by
   enumeration. Deciding by differentiation is not generic either, for
   a sharper reason than "needs a unary operation": it recurses on the
   carrier, and it re-indexes the slot family at each step, so it needs
   decisions at *every* element rather than at the parts of one
   splitting. `RegularExpression` is now unblocked.
2. **`SequentialUnambiguity` + `Greedy` (7 files).** Both need
   equidivisibility (Levi's lemma), which is a genuine property of the
   theory — true for free monoids, false for commutative ones. It should
   be a named hypothesis on the promodel, not ambient.
3. **`Coinductive` (4 files).** Needs a greatest-fixed-point counterpart
   to `Inductive`'s `μ`. Not blocked on anything but volume.
4. **`Subgrammar` (2 files).** Additive; nothing in the way.
5. **`Later/{Box,Infix}`.** `Infix` is the two-sided order — the CYK
   shape — and is the one worth having, since it is what the bag
   instance would want.

Three things are *stated but unbuilt*, and they matter more than any of
the above:

- `⊤ ≅ μ(shape)` as the generic replacement for `⊤ ≅ String`. The
  decomposition axiom exists per-instance (`charCase`, `bagCase`); what
  is missing is the generic `μ` of the shape functor, forded so
  `resultSort o` is not a stuck index.
- `⊗ ⊣ ⊸` as a single `Iso`. Both sides have definitional β/η
  *separately*; making them definitionally inverse to each other needs
  the promodel's focused and unfocused splittings to be definitionally
  inverse — true for strings, not automatic.
- `permTrans` / `permInsert` / `mergePerm`, which is what stands between
  `merge : Bag → Bag → Bag` and an internal `Bagged ⊗ Bagged ⊢ Bagged`.
