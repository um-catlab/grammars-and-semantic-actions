# Instance audit: duplication, boundaries, and eDSL discipline

Read-only pass over `Instances/{Strings,Bags,Lambda}` against three
questions: what should be generic, where is the phase boundary leaking,
and are the examples actually in the language.

Headline: **`Strings` is largely in good shape; `Bags` is not.** Bags was
written first and never got the corrections Strings did, so it is
carrying private copies of the combinator layer, an external resource
predicate, and algorithms that are Agda functions rather than terms.

---

## 1. Reusable components that should be pulled out

### 1a. The monoid signature exists twice, byte-identically

`Strings/Base.monSig` and `Bags/Base.cmSig` are the same four copattern
lines over the same `MonOp` / `MonAr`. Bags calls it `cmSig`, but
commutativity is an **equation**, not a signature difference — the
signature of commutative monoids *is* the signature of monoids.

→ one `Theories/Monoid.agda` exporting `MonOp`, `MonAr`, `monoidSig`,
and the nullary-splitting predicate `IsNil` (also duplicated). Both
instances then differ only in `Split`, which is the point.

### 1b. Bags rebuilds the combinator layer privately — the biggest one

`Strings/Base.agda` opens `TheoryGrammar.RulesFib`. **`Bags/Base.agda`
does not.** So `Bags/Connectives.agda` contains private copies of

    ⊤'  idg  _∘g_  ⊕-elim  ⊕ᴰ-in  ⊕ᴰ-elim  liftg  ⊗-map  ⊗I  ⊗E

≈46 lines re-deriving what the generic layer already provides. This is
exactly the failure mode `RulesFib` was created to end, and Bags predates
it.

→ `open RulesFib bagFib public` in `Bags/Base.agda`, delete the copies.
Expect a `⊕-elim`/`⊕-E` naming collision, as happened in
`Strings/KleeneStar`. **Highest value per unit of work in this document.**

### 1c. `decΠBool` is generic but unused by Bags

It lives in `TheoryGrammar/Enumerable.agda`. Bags hand-rolls the
Bool-slot combination in `mfGuarded` and in quicksort's `decCut`.

### 1d. NOT duplication, and worth saying so

`split3LenL/R/L</R<` (Strings) and `ilvLenL/R/L</R<` (Bags) look like
duplicates but are not. The *statement* is already generic — it is
`deg≤` and `deg<` in `GradedSubstrate` — and only the instance proofs
differ, by induction on different splitting families. That is the
intended shape and should be left alone.

---

## 2. Abstraction-boundary violations

### 2a. Bags' resource predicate is still external

    Bags/Mergesort.agda:  NonEmpty m = 0 < length m
                          Small    m = length m ≤ 1

Strings fixed precisely this: `NonTrivial = ⊕ᴰ Char (λ c → ⌈ c ∷ [] ⌉ ⊗ ⊤)`,
built from `⌈_⌉`, `⊗`, `⊕ᴰ`, `⊤` and nothing else. The bag analogue is
`⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗ ⊤)` — which is *already what `bagCase`
produces*, so the definition is sitting there unused.

Consequence, as at Strings: `StrProper` became the internal predicate and
several conversions vanished. The same should happen to `Proper'`.

### 2b. Metalanguage predicates as parameters

    partition   : (p  : A → Bool) …
    splitAround : (le : A → A → Bool) …
    module Sort   (le : A → A → Bool)
    module MSort  (le : A → A → Bool)

`Bool`-valued predicates where the calculus has `⊕` and `Dec⟨_⟩`. A
comparison should enter as a decision, not a boolean.

### 2c. Agda functions on carriers, only one of them marked

`merge`, `partition`, `dealt` are all `Bag → …` functions. `merge` is
documented as such with the three lemmas its internalisation needs;
`partition` and `dealt` are not marked at all.

### 2d. Lambda — not assessed

Only 1 of 14 files under `Instances/Lambda/` references the shared layer,
which *may* indicate the same problem as 1b. It is another agent's
in-flight work and I have not read it; flagging for its owner rather than
asserting a finding.

---

## 3. Examples that are Agda, not eDSL

### 3a. No bag algorithm is a `⊢` term

    quicksort  : Bag → Bag
    quicksortV : (m : Bag) → Σ[ out ∈ Bag ] Perm out m
    mergesort  : Bag → Bag

`quicksortV` carries exactly the data of `⊤ ⊢ Spec` — same information,
written as an Agda function. Restating the three as

    quicksort  : ⊤ ⊢ Bagged
    quicksortV : ⊤ ⊢ Spec
    mergesort  : ⊤ ⊢ Bagged

is nearly mechanical and is the difference between "an Agda program that
happens to call `hyloC`" and "a term of the calculus". This is the single
clearest instance of the thing the discipline exists to prevent.

### 3b. `parseAB` builds with container constructors

`Strings/Examples.parseAB` uses `G.sup` directly — shapes, positions and
absurd-pattern position functions. That is phase-1 vocabulary in an
example. It should go through the description's intro rules.

### 3c. Legitimately external, for contrast

`decEqS`, `allRules`, `allComplete`, `matchLit` in `Strings/Examples` are
**parameters** to `Decide` — instantiation data supplied from outside,
not reasoning inlined into a program. `matchLit` is even a `⊢` term. This
is where the boundary is correctly drawn, and is the standard the rest
should meet.

---

## Ranked

| | work | payoff |
|---|---|---|
| 1 | `Bags/Base` opens `RulesFib`; delete ~46 lines of copies | removes the largest duplication |
| 2 | retype the three bag algorithms as `⊤ ⊢ …` | the examples become eDSL |
| 3 | Bags' `NonTrivial`, mirroring Strings | removes external length-talk |
| 4 | shared `Theories/Monoid.agda` | de-duplicates the signature |
| 5 | `parseAB` via intro rules | example stops using `sup` |
| 6 | `le` as a decision rather than a `Bool` | closes 2b |

1–3 are independent of each other and none touches files another agent is
editing.
