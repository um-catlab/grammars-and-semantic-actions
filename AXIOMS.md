# Axioms of the dependent Lambek development

Notes on **what is actually assumed** by the grammar / dependent-Lambek
calculus, and an audit of every place we unfold an `opaque` definition.

The model is the presheaf category on the **discrete** category `String`
(`String = List ⟨Alphabet⟩`, an hSet) with **Day convolution** for `⊗`:

| construct | model definition | role |
|---|---|---|
| `Grammar ℓ` | `String → Type ℓ` | presheaf |
| `A ⊢ B` | `∀ w → A w → B w` | natural transformation |
| `&, ⊕, ⊤, ⊥` | pointwise `×, ⊎, Unit, ⊥` | bicartesian structure |
| `⊕ᴰ, &ᴰ` | pointwise `Σ, Π` | indexed (co)products |
| `_⊗_` | `Σ[s ∈ Splitting w] A(left s) × B(right s)` | Day convolution of `(List,++,[])` |
| `ε` | `w Eq.≡ []` | Day unit |
| `_⊸_, _⟜_` | Day hom | residuals |
| `literal c` | `w Eq.≡ [ c ]` | generator |
| `⌈ w ⌉` | `literal c₀ ⊗ … ⊗ ε` | representable `よ w` |
| `μ` | initial algebra | least fixpoint |

In the cubical model **every grammar fact is a theorem** — there are no
`postulate`s in the calculus, no `REWRITE` rules, no `primTrustMe`. The
single `postulate` in the tree (`String/Unicode.agda`) is about a concrete
alphabet, not the calculus. So "axiom" below means *the fundamental
semantic truth a **syntax** would take as primitive*, not a literal
`postulate`.

---

## The assumed axioms

### 0. Standing hypothesis
**`Alphabet : hSet ℓ-zero`** — the alphabet is a set. Hence `String` is an
hSet and `Eq.≡` on strings is a proposition. (Module parameter, discharged
at instantiation.)

### 1. Two string-specific primitives
Everything string-specific reduces to these two. Both are *definitions /
theorems* in the model; they are exactly what a syntax would postulate.

- **(FM) `String` is the free monoid on `Alphabet`.** `String = List
  Alphabet`, `ε = (− Eq.≡ [])`, `⊗ = Day convolution of (List,++,[])`.
  Generates: `⌈ u ++ v ⌉ ≅ ⌈u⌉ ⊗ ⌈v⌉`, `⌈[]⌉ ≅ ε`; **equidivisibility /
  Levi** (`split++`); **cancellation** (`++-cancelˡEq`, `++-cancelʳEq`,
  snoc); **unique readability** (every string *is* its char list).

- **(REP) `literal c` is the representable at `[c]`.** `literal c w ≃ (w
  Eq.≡ [c])`. Generates: `⌈ w ⌉` representable for all `w` —
  `mk⌈⌉ : ⌈w⌉ w`, `uniquely-supported-⌈⌉Eq : ⌈w⌉ w' → w Eq.≡ w'`,
  `pick-parse : A w ≃ (⌈w⌉ ⊢ A)`, `⌈⌉≅⌈⌉Eq` (induction on `w` via FM's `⊗`).

These bundle into **one** statement: *`よ : String → Grammar`, `よ w = ⌈w⌉`,
is the strong-monoidal Yoneda embedding of the free monoid `String`, with
`literal c = よ[c]`.* FM and REP are its two halves.

### 2. Ambient logic (definitions, not in question)
Bicartesian-closed structure (`&,⊕,⊤,⊥,⊕ᴰ,&ᴰ`), Day-monoidal-closed
structure (`⊗,ε,⊸,⟜`), and initial algebras (`μ`). `μ`'s well-foundedness
is **trusted** via `{-# TERMINATING #-}` in `Grammar/Inductive/HLevels`,
`Grammar/Inductive/Indexed`, `Grammar/Coinductive/Indexed` — the one place
"the semantics is well-founded" is assumed rather than checked.

### 3. The only literal `postulate`
`mkUnicodeCharPath-yes/no` (`String/Unicode.agda`): JS `primCharEquality`
decides `≡` on Unicode chars. Alphabet instantiation; not the calculus.

### Everything else is downstream
- `⊤ ≅ ⊕[w∈String] ⌈w⌉` — REP (+ String hSet): `Σ[w](w Eq.≡ w')` contractible.
- `⊤ ≅ char *` (`string≅⊤`) — FM (unique readability) + `μ`-induction.
- `⌈w⌉ & ⌈v⌉ ≅ ⊕[w Eq.≡ v] ⌈w⌉` — REP + String-is-a-set (product of
  representables on a discrete index = sum over hom-equality).
- splitting trichotomy / `⊗&-distL≅` — Levi (FM) reflected through REP.
- char/⌈⌉ distributions (`Tiny`) — REP + FM cancellation.

The earlier "A/B/C" framing was redundant: monoidal-`⌈⌉` is FM; density is
REP. There is essentially **one** semantic primitive (Yoneda embedding of
the free monoid), trusted `μ`-termination, and one orthogonal alphabet
postulate.

---

## Opaque-unfold audit

`opaque`/`unfolding` is the project's escape hatch into the model. Unfolding
is **sanctioned** when:
- **(P)** defining a primitive or its intro/elim/β/η laws;
- **(A)** defining an axiom (FM/REP realisations: `mk⌈⌉`,
  `uniquely-supported-⌈⌉Eq`, `slice≅`);
- **(S)** acting as a *rudimentary definitional-equality solver* — exposing
  the underlying `Σ/×/⊎` to witness a `≡` that holds definitionally
  (e.g. an iso's `sec`/`ret`).

It is **worrisome** when a *derived* result unfolds `_⊗_ / _&_ / literal /
the-split / same-parses` to re-derive something **existing primitives
already give** (REP's `uniquely-supported-⌈⌉Eq` / `pick-parse`, the
keystone `slice≅`, `⊗-reflect`). Those are flagged below to revisit.

203 `unfolding` sites total. Connective `Base.agda` modules (defining the
logic) are **(P)** wholesale and not enumerated. Application code
(`Examples/`, `Parser/`, `Thompson/`, `Lex/`, `Automata/`,
`String/ASCII`) unfolds for witness construction / refl-evaluation —
**(S)**, not audited line-by-line here.

### Core / axiom-layer — verdicts

| site | unfolds | verdict |
|---|---|---|
| `Yoneda/Base.agda:60` (`slice≅`) | `_&_ &-intro` | **(A) OK** — the keystone; the single sanctioned model-touch realising REP/Yoneda. |
| `String/Base.agda:64,82,104,144,170` (`mk⌈⌉`, `uniquely-supported-⌈⌉Eq`, `⌈⌉≅⌈⌉'`, `⌈⌉≅⌈⌉Eq`) | `⊗-intro ε literal _⊗_ mk⌈⌉ …` | **(A) OK** — defines the REP axiom layer. |
| `Subgrammar/Base.agda:38–194` | `⊤ true subgrammar sub-π sub-intro` | **(P) OK** — defines the subgrammar primitive + its laws. |
| `Derivative/Base.agda:40,61` (`√l`,`√r`) | `_⟜_ _⊸_ literal _⇒_ ⊤` | **(P) OK (borderline)** — defines the Brzozowski-derivative primitive. |
| `Distributivity.agda:70,95,123` | `⇒-intro &-intro π₁ _⊕_ ⊕-elim` | **(S) OK** — witnesses the BCC distributive isos. |

### FLAGGED — revisit (worrisome)

| site | unfolds | why flagged |
|---|---|---|
| **`Yoneda/Reflect.agda:104`** (`⊗&-distL-fun` + `sec`/`ret`) | `_&_ _⊗_ ⊥` | The boundary lemma is proven **pointwise**. It *could* bootstrap on `slice≅` + `⊗-reflect` + index-level Levi and never unfold `_⊗_ _&_`. Known optional-polish item. |
| **`Yoneda/Reflect.agda:63`** (`⌈⌉-prefix-push`) | `_⊗_ _&_` | Representable-pinned merge. Uses REP (`uniquely-supported-⌈⌉Eq`) — good — but still unfolds `_⊗_ _&_` pointwise instead of going through `slice≅`. Mild. |
| **`Literal/Properties.agda:33,41`** (`same-literal`, `same-first`) | `_&_ literal ⊥ _⊗_` | Re-derives the representable-product fact `＂c＂&＂c'＂ ≅ ⊕[c≡c']＂c＂` by hand. This is the single-char case of `⌈w⌉&⌈v⌉ ≅ ⊕[w Eq.≡ v]⌈w⌉`, which follows from REP. Should be derived, not hand-unfolded. |
| **`SequentialUnambiguity/Properties.agda:34,111`** | `the-split _⊗_ ⊗-intro _&_ literal` | `⊛→unique-splitting`-style proofs doing raw splitting surgery. Candidate to rebuild on REP / `slice≅` (same spirit as the retired trichotomy). |
| **`External/String/Tiny.agda`** (15 sites, esp. `unique-splitting-*`, the `≅` `sec`/`ret`) | `the-split _⊗_ literal _&_ unique-splitting-charR …` | The `unique-splitting-charL/R/⌈⌉L/R` lemmas re-derive splitting-uniqueness by hand — exactly what REP's `uniquely-supported-⌈⌉Eq` provides. The ⌈⌉-pinned lemmas dissolve into the keystone (see `⌈⌉-prefix-push` in `Yoneda/Reflect`); the char-pinned ones are inherent snoc-cancellation (already clean). On the retirement list. |
| **`Box/Properties.agda`** (13 sites, e.g. `:150,:203,:558,:602`) | `the-split _⊗_ same-parses √l-cat …` | Active WIP (Box branch). Several unfold `uniquely-supported-⌈⌉Eq` (good, REP) but also `the-split`/`same-parses` (raw surgery). Audit per-site when the Box work settles; likely several can route through REP/`slice≅`. |

### Notes
- **(P)** primitive-definition modules (not flagged): `LinearFunction/Base`,
  `LinearProduct/{AsPath,AsEquality}/Base`, `Sum/Binary/AsPrimitive/Base`,
  `Product/Binary/AsPrimitive/Base`, `Top/{Base,Properties}`,
  `Bottom/{Base,Properties}`, `Epsilon/AsEquality/*`, `Function/AsPrimitive/Base`,
  `Equalizer/Base`, `KleeneStar/Inductive/Base`, `Inductive/HLevels`,
  `Lift/Properties`, and the `*/Properties` proving each connective's own laws.
- The retirement of `Grammar/External/LinearProduct/SplittingTrichotomy.agda`
  (775 lines) already removed its large block of worrisome unfolds; its
  replacement lives in `Grammar/Yoneda/{Base,Reflect}`.
