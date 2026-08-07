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
| Later | 7 | `Graded` (`WFLater`, `hyloC`) | **done** — `Infix` subsumed, see below |
| Subgrammar | 2 | `Subgrammar` (`Compr`) | **done** |
| Derivative | 3 | `Derivative` (`δ`, `DerivTensor`) | **done** |
| SequentialUnambiguity | 5 | `Instances/Strings/SeqUnambig` | **core done** |
| Greedy | 2 | `Instances/Strings/Greedy`, `Graded` (`Automaton`) | **done** |
| RegularExpression | 2 | `Instances/Strings/RegExp` | **done** |
| Coinductive | 4 | `Inductive` (`ν`), `Hylo` (`ν-η`, `μ≅ν`) | **done** |
| String, External | 12 | — | *replaced*, not ported |

So the additive half is done, the multiplicative core is done, and what
remains is **6 files in two groups**, plus `Later/{Box,Infix}`,, each blocked on one identifiable
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
2. **`SequentialUnambiguity` + `Greedy`.** The blocker is gone:
   **Levi's lemma is five clauses** over the inductive `Split3` — a
   double recursion with no arithmetic, no `split++`, no length
   induction. Same payoff the derivative got, in a second place. It is
   still a genuine property of the theory (false for bags), so it stays
   instance-level.

   On top of it, `First` and `FollowLast` are recast as **derivatives
   rather than subsets of the alphabet**: `c ∉First A` *is* `δ_c A ⊢ ⊥`.
   That deletes the `Powerset.More` and truncation machinery the
   original carried — they are grammars, so they are compared with `⊢`
   like everything else. `sameSplit` then proves that under `A ⊛ B` a
   word has at most one splitting compatible with A and B.

   Two findings to carry forward:

   * **`⊛` does not give `DecReadable`.** `fromUnique` consumes
     `splitProp` — "the *promodel* has at most one decomposition" —
     which is flatly false for strings and no amount of sequential
     unambiguity changes it. What `⊛` buys is uniqueness *relative to
     the grammars*, and the existing interface has nowhere to say that.
     The honest fix is a grammar-relative unique-readability
     constructor in `Decidable/Tensor.agda`; it should be made
     deliberately rather than by bending `DecReadable`.

   * **K bites three times** once `Char` is not assumed discrete.
     Matching two `Split3`s against each other, `cons` injectivity, and
     inverting a literal's splitting all leave the unifier a reflexive
     equation on `Char`. Each is fixed the same way — count, or `ap` a
     projection, never unify two heads. `Greedy` will hit this
     constantly, so it is worth knowing up front.

   `Greedy/Base` is now `Instances/Strings/Greedy`, and it stays a
   string instance for the reason bucket 3 gives: there is no
   "leftmost" for bags. What ported for *free* is the residual it
   needs — "a G-parse of `w ++ v`, as a grammar in `v`" is exactly the
   **derivative with the left slot pinned to `w`** instead of to a
   single character. `Derivʷ` is `ActOf` at a different rest-tuple and
   `actʷ-β` is `refl`; nothing new is defined. That is the `Assembly`
   parameter earning its keep for the third time.

   **`Greedy/Automata` did not need porting — it needed deleting.**
   Upstream builds automata as a bespoke record with its own run
   function and its own recursion. All of that is three notions the
   tree already had, and none of them are about strings:

   * an **automaton is an algebra** for a description (`AlgC`). A DFA's
     transition table is one way to *build* one, not a separate notion
     — and an algebra may have an infinite carrier, which a DFA may not.
   * **⊤ carries a coalgebra** for the description exactly when the
     theory can take an element apart one step along it. That is the
     decomposition axiom (`charCase`, `bagCase`) — naming it `Scanner`
     says what it always was.
   * the description being **guarded** is local contractivity.

   Given those, **running an automaton is `hyloC`** — no recursion at
   the use site, and the termination certificate *is* the guardedness.
   `Automaton`/`Scanner`/`runAut` therefore live in `Graded` beside
   `hyloC`, mention neither strings nor even the signature's
   operations, and any theory with a decomposition axiom gets automata
   for free.

   `Instances/Bags/Automata.agda` is the check that this is real: the
   same three per-theory pieces over a **commutative** theory, same
   runner. It also surfaces something the string case hides — over a
   commutative theory the scanner *chooses* a decomposition, so the
   answer is canonical only when the algebra is invariant under the
   theory's equations. `sum`/`size` qualify; "build a list" does not.
   The type does not stop you writing the latter, it just stops meaning
   what you wanted.
3. ~~**`RegularExpression`**~~ — **done**, and bucket 3's classification
   of it as *string-specific* was right: the derivative-based matcher
   recurses on the carrier, which is not something `Fibered` provides.
   It lives at `Instances/Strings/RegExp.agda`.

   The design point worth reusing: **the syntax is indexed by its
   nullability**. That index is not bookkeeping. `KleeneStar` already
   needed `NonNullable A` for `A *` to be guarded, and non-nullability
   is *also* exactly what makes `δ_c (r ⋆) = δ_c r · r ⋆` correct — one
   hypothesis doing two jobs, so it belongs in the type. `_⋆` takes a
   `RegExp false` and nothing further is checked; in the whole
   correctness proof the index is consumed in exactly one place, the
   `nil` case of the star's completeness.

   The matcher `decRE` **decides the denotation**, so there is no
   correctness theorem about the matcher at all — only about `δᵣ`.
   That correctness is a logical equivalence rather than an Iso, and
   deliberately: at `r · s` with `r` nullable the classical law
   replaces `r` by `ε`, forgetting *which* ε-parse `r` had. For an
   unambiguous regex that is no loss; for an ambiguous one it is
   precisely the ambiguity, and a parser (as opposed to a matcher)
   would have to keep it.
4. **`Coinductive`** — core done, and it was **not** just volume.
   `ν` sits next to `μ` inside `Ind` (a separate module would mean a
   second application of `Ind`, and two applications of a parameterised
   module make every shared name ambiguous — a trap that cost time
   twice in this session).

   The measured result: **splitting the record into `shOf`/`nxOf`
   removes upstream's first `{-# TERMINATING #-}`.** Upstream's `ν` has
   one field `unroll : ⟦ F x ⟧ (ν F) w`, burying the recursive
   occurrence under a Σ and a function type, so `corecHomo` needs the
   pragma; here `unfold` is productive unaided. That mirrors `μ`, which
   needs no `NO_POSITIVITY_CHECK` here for the same structural reason.

   Two things it does *not* fix, both verified rather than assumed:

   * `into-out` is **not** `refl`. Agda withholds η from coinductive
     records (it would let the productivity checker be fooled), so the
     round trip is a one-line copattern on the interval instead.
   * **`coind` (uniqueness) still needs the pragma.** `ϕ` agrees with
     `unfold` on `shOf` by `cong fst` of the homomorphism square and on
     `nxOf` by `cong snd` composed with the corecursive call — but that
     call sits under `funExt`, which is not a guard, so termination
     checking fails. Upstream carries a second `{-# TERMINATING #-}`
     for it. Not taken here: this tree has no unsafe pragmas and should
     not acquire one as a side effect of a port. The choice is (a) the
     pragma or (b) a real cubical bisimulation argument.

   `coind` is needed only to package ν as a c-c-l `TerminalCoalgebra`;
   every computational use of ν is covered.
5. ~~**`Subgrammar`**~~ — **done**, and it confirms the classification:
   it needs *no signature at all*. `Compr` lives at `CarrierNotation`,
   the same level as `&` and `⊕`, because comprehension is pointwise in
   the index like every additive connective. `Grammar/Subgrammar/`
   imports the whole of `Grammar` and uses nothing multiplicative.

   One design change, and it is the same lesson as `DerivTensor`:
   **state the side condition as the predicate, not as an equation.**
   Upstream writes it as `p ∘g f ≡ true ∘g ⊤-intro` and then pays —
   `insert-pf` builds that equation out of the predicate via
   `hPropExt`, `extract-pf` transports back out, and both are `opaque`
   with an `unfolding` discipline. Writing `Holds f = ∀ w x → ⟨ p w (f w x) ⟩`
   deletes all of it: the UP is an `Iso` with **both round trips
   `refl`**, no `Σ≡Prop`, no `hPropExt`, no `transport`, no `opaque`.
   β was already `refl` upstream; η was not, and is here by Σ's η. The
   equational phrasing is still available (`toEqn`/`ofEqn`) — it just
   costs `hPropExt` once, in one place, instead of at every use site.
6. ~~**`Later/{Box,Infix}`**~~ — **resolved, and the earlier note here
   was wrong.** It claimed `Infix` was "the one worth having". It is
   not: `▷ⁱ` is built on the *proper-substring* order, which is
   strictly **finer** than `Graded`'s degree order (a proper infix is
   shorter, but not every shorter string is an infix). A finer order
   means fewer `j ≺ i`, hence **fewer** assumptions in the löb step —
   so `▷ⁱ` is *implied* by the graded `▷`, not the other way round.
   `▷-mono` in `Graded.agda` proves exactly this, and
   `Instances/Strings/CYK.agda` is the evidence: it was built on
   `Guarded` and never needed an infix modality.

   What *was* worth doing is the TODO in `Graded.agda`'s own header —
   "the order can be made abstract later". Done: `WFLater` takes a
   relation and its well-foundedness and defines `▷`/`next`/`löb`
   without ever mentioning the degree. The graded order is now one
   instance (`open WFLater _≺_ ≺-wf public`, so every downstream name
   is unchanged), and upstream's `Later/Ordered` — generic in a
   `WFOrder`, instantiated at the suffix and infix orders — is another.
   This is what unblocks a lexicographic instance if one is ever
   needed.

   `Box` is the cofree comonad of the modality and is not required by
   anything in this tree.

Three things are *stated but unbuilt*, and they matter more than any of
the above:

- ~~`⊤ ≅ μ(shape)`~~ — **built** (`Automaton.agda`), and the stated
  blocker turned out to be avoidable. It said `μ` cannot be a motive at
  `ℓSh`. True, but irrelevant: `löb` is level-polymorphic, so building
  the parse *directly* by löb never mentions `⟦_⟧c` and never meets the
  constraint. Only `shapeOf` is needed from the scanner, since the
  coalgebra is carried by ⊤ and its payloads are trivial.

  `scanμ` gives **existence unconditionally**: any theory with a
  decomposition axiom and a guarded description parses every element.
  `Free F = ∀ i → isContr (μ F i)` is **uniqueness**, and it is exactly
  what separates theories — strings have it, bags do not (a multiset
  comes apart in `|m|!` orders). So the commutative-theory caveat is
  now a property rather than a warning:
  `scanμ-scanner-irrelevant` says the parse is independent of the
  scanner *precisely when the theory is free*.
- `⊗ ⊣ ⊸` as a single `Iso`. Both sides have definitional β/η
  *separately*; making them definitionally inverse to each other needs
  the promodel's focused and unfocused splittings to be definitionally
  inverse — true for strings, not automatic.
- `permTrans` / `permInsert` / `mergePerm`, which is what stands between
  `merge : Bag → Bag → Bag` and an internal `Bagged ⊗ Bagged ⊢ Bagged`.
