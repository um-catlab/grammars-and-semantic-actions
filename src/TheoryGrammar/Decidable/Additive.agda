{-
  Decidability as a CONNECTIVE, additively.  Needs only a `Model` --
  nothing here mentions the operations.

  A decision for `A` with complement `A'` is a map `⊤ ⊢ A ⊕ A'` together
  with the exclusion `(A & A') ⊢ ⊥`, without which `⊕-I₂ ∘ ⊤-I` would
  "decide" everything at `A' = ⊤`.  `¬G A = A ⇒ ⊥` is proved to be the
  LARGEST complement (`largest`), so normalising to the default
  `Dec⟨ A ⟩ = A ⊕ ¬G A` loses nothing -- `toDec` does it.

  Every proof below is a composite of `Rules`' intro/elim except the
  POINTWISE elimination `⊕-E-at` and its specialisation `dec-elim`.
  Those ARE elimination rules, so like `Rules.⊕-E` they match the sum;
  instances never may.  No `Dec`, no `yes`/`no` anywhere.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import TheoryGrammar.Base
open import TheoryGrammar.Rules

private variable ℓS ℓ ℓ' ℓX ℓA ℓB ℓC ℓY ℓZ : Level


module DecAdd {S : Type ℓS} (Car : S → Type ℓX) where

  open CarrierNotation Car public
  open RulesCarrier Car public

  private variable
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s

  -- INTERNAL LOGICAL EQUIVALENCE: the two maps, nothing else.  Not a
  -- decision notion, but it belongs with the additives -- it mentions
  -- only `_⊢_`, so it needs nothing but the carrier, and every instance
  -- that states "these two grammars are the same predicate" wants it.
  -- (It was written out locally in `Instances/Field/Partial`; that copy
  -- is gone and reads this one.)
  _⊣⊢_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓX (ℓ-max ℓA ℓB))
  A ⊣⊢ B = (A ⊢ B) × (B ⊢ A)

  infix 1 _⊣⊢_

  -- internal negation
  ¬G_ : TheoryTy ℓA s → TheoryTy ℓA s
  ¬G A = A ⇒ ⊥G

  infix 32 ¬G_

  -- the default complement: internal negation
  Dec⟨_⟩ : TheoryTy ℓA s → TheoryTy ℓA s
  Dec⟨ A ⟩ = A ⊕ ¬G A

  -- The introduction rules, with the grammar NAMED.  Naming it is not
  -- optional: `Dec⟨ A ⟩` unfolds to `A ⊕ ¬G A`, and a grammar-valued
  -- implicit cannot be recovered from `?A m ⊎ ?B m` once `m` is already
  -- in the metavariable's context.
  dec-yes : (A : TheoryTy ℓA s) → A ⊢ Dec⟨ A ⟩
  dec-yes A = ⊕-I₁ {A = A} {B = ¬G A}

  dec-no : (A : TheoryTy ℓA s) → ¬G A ⊢ Dec⟨ A ⟩
  dec-no A = ⊕-I₂ {B = ¬G A} {A = A}

  -- ================================================================
  -- THE ELIMINATION RULE, AT A POINT.
  --
  -- `Rules.⊕-E` eliminates a sum UNIFORMLY in the index: its branches
  -- are maps of the calculus, given at every `m` at once.  Many uses of
  -- a decision cannot be uniform, because the data the branches need
  -- exists only at ONE index -- deciders supplied for the splittings of
  -- THIS `m`, a refutation transported along unique readability at THIS
  -- `m`, a recursive call at THIS subterm.  Not even the CONSTANT
  -- motive helps: `⊕-E`'s branches still quantify over the index.
  --
  -- So the elimination has to be available at a point, and that is
  -- `⊕-E-at`.  It is a genuine ELIMINATION RULE, and like `Rules.⊕-E`
  -- it is therefore defined by matching `inl`/`inr`; `⊕-E` factors
  -- through it (`⊕-E f g m = ⊕-E-at _ _ m (f m) (g m)`), so nothing new
  -- is assumed -- only the quantifier is moved.
  --
  -- THE DISCIPLINE, stated here because this is where it is enforced:
  -- the FRAMEWORK may match a sum, at its own elimination rules, which
  -- are exactly `Rules.⊕-E`, `⊕-E-at` and `⊕-E-atᴰ`.  INSTANCES may
  -- not: they call `dec-elim`.  Every `with`-on-a-decision that used to
  -- appear in an instance is one application of it.
  -- ================================================================

  ⊕-E-at : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s) (m : Car s)
           {Z : Type ℓZ}
         → (A m → Z) → (B m → Z) → (A ⊕ B) m → Z
  ⊕-E-at A B m f g (inl x) = f x
  ⊕-E-at A B m f g (inr y) = g y

  -- the dependent form, whose motive may mention the sum itself.  Used
  -- when the branch has to prove something ABOUT the decision it read.
  ⊕-E-atᴰ : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s) (m : Car s)
            {Z : (A ⊕ B) m → Type ℓZ}
          → ((x : A m) → Z (inl x)) → ((y : B m) → Z (inr y))
          → (d : (A ⊕ B) m) → Z d
  ⊕-E-atᴰ A B m f g (inl x) = f x
  ⊕-E-atᴰ A B m f g (inr y) = g y

  -- `⊕-E` factors through the pointwise rule: the two are the same fact
  ⊕-E-at-factors : {C : TheoryTy ℓC s} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
                   (f : A ⊢ C) (g : B ⊢ C) (m : Car s) (d : (A ⊕ B) m)
                 → ⊕-E f g m d ≡ ⊕-E-at A B m (f m) (g m) d
  ⊕-E-at-factors A B f g m = ⊕-E-atᴰ A B m (λ _ → refl) (λ _ → refl)

  -- and its specialisation to a decision, which is what instances use
  dec-elim : (A : TheoryTy ℓA s) (m : Car s) {Z : Type ℓZ}
           → (A m → Z) → ((¬G A) m → Z) → Dec⟨ A ⟩ m → Z
  dec-elim A m = ⊕-E-at A (¬G A) m

  dec-elimᴰ : (A : TheoryTy ℓA s) (m : Car s)
              {Z : Dec⟨ A ⟩ m → Type ℓZ}
            → ((x : A m) → Z (dec-yes A m x))
            → ((k : (¬G A) m) → Z (dec-no A m k))
            → (d : Dec⟨ A ⟩ m) → Z d
  dec-elimᴰ A m = ⊕-E-atᴰ A (¬G A) m

  -- ================================================================
  -- The additive lemmas the decision combinators are built from.
  -- ================================================================

  &-swap : (A & B) ⊢ (B & A)
  &-swap = &-I &-E₂ &-E₁

  -- ex falso: a grammar and its negation are jointly empty
  contra : (A & ¬G A) ⊢ ⊥G
  contra {A = A} = ⇒-app ∘⊢ &-swap

  -- `&` distributes over `⊕`.  `⊕-E` under a `⇒`, then uncurry: proved
  -- from intro/elim alone, with no case split on the sum.
  dist& : ((A ⊕ B) & C) ⊢ ((A & C) ⊕ (B & C))
  dist& = Iso.inv ⇒-UP (⊕-E (⇒-I ⊕-I₁) (⇒-I ⊕-I₂))

  -- contravariance of negation
  ¬G-map : B ⊢ A → ¬G A ⊢ ¬G B
  ¬G-map g = ⇒-I (contra ∘⊢ &-I (g ∘⊢ &-E₂) &-E₁)

  -- de Morgan, the constructive direction: what refuting a sum needs
  deMorgan : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
           → (¬G A & ¬G B) ⊢ ¬G (A ⊕ B)
  deMorgan A B =
    ⇒-I (⊕-E (contra ∘⊢ &-I &-E₁ (&-E₁ ∘⊢ &-E₂))
             (contra ∘⊢ &-I &-E₁ (&-E₂ ∘⊢ &-E₂))
         ∘⊢ (dist& ∘⊢ &-swap))

  -- ================================================================
  -- COMPLEMENTS.  A decision is only informative if its two halves
  -- exclude each other -- without that, `⊕-I₂ ∘⊢ ⊤-I` "decides" every
  -- A at A' = ⊤G and says nothing at all.  So a decision carries the
  -- exclusion, and `¬G A` is characterised as the LARGEST complement:
  -- every other one factors through it, which is why nothing is lost by
  -- normalising to `Dec⟨ A ⟩`.
  -- ================================================================

  Complement : TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓX (ℓ-max ℓA ℓB))
  Complement A A' = (A & A') ⊢ ⊥G

  -- A `Decision A A'` denotes: `A'` decides `A`.  The two fields are the
  -- two halves of that, and NEITHER alone is it -- `decide` without
  -- `exclude` is satisfied by `A' = ⊤G`, and `exclude` without `decide`
  -- by `A' = ⊥G`.
  record Decision (A : TheoryTy ℓA s) (A' : TheoryTy ℓB s)
    : Type (ℓ-max ℓX (ℓ-max ℓA ℓB)) where
    field
      -- at least one of the two holds, everywhere
      decide  : ⊤G ⊢ (A ⊕ A')
      -- ... and never both
      exclude : Complement A A'

  open Decision public

  -- `¬G A` is a complement ...
  ¬G-excludes : (A : TheoryTy ℓA s) → Complement A (¬G A)
  ¬G-excludes A = contra {A = A}

  -- ... and the largest one: any complement embeds into it
  largest : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
          → Complement A A' → A' ⊢ ¬G A
  largest d = ⇒-I (d ∘⊢ &-swap)

  -- so every decision, at whatever complement, yields the default one
  toDec : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
        → Decision A A' → ⊤G ⊢ Dec⟨ A ⟩
  toDec {A = A} D = ⊕-E (dec-yes A) (dec-no A ∘⊢ largest (D .exclude)) ∘⊢ D .decide

  -- and the default one is a decision
  decDefault : (A : TheoryTy ℓA s) → ⊤G ⊢ Dec⟨ A ⟩ → Decision A (¬G A)
  decDefault A f .decide  = f
  decDefault A f .exclude = ¬G-excludes A

  -- ================================================================
  -- Closure properties of decidability.
  -- ================================================================

  -- along an internal logical equivalence
  dec-map : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
          → A ⊢ B → B ⊢ A → Dec⟨ A ⟩ ⊢ Dec⟨ B ⟩
  dec-map A B f g = ⊕-E (dec-yes B ∘⊢ f) (dec-no B ∘⊢ ¬G-map g)

  -- under `⊕`: two distributions and a de Morgan
  dec-⊕ : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
        → (Dec⟨ A ⟩ & Dec⟨ B ⟩) ⊢ Dec⟨ A ⊕ B ⟩
  dec-⊕ A B =
    ⊕-E (dec-yes (A ⊕ B) ∘⊢ (⊕-I₁ ∘⊢ &-E₁))
        (⊕-E (dec-yes (A ⊕ B) ∘⊢ (⊕-I₂ ∘⊢ &-E₁))
             (dec-no (A ⊕ B) ∘⊢ (deMorgan A B ∘⊢ &-swap))
         ∘⊢ (dist& ∘⊢ &-swap))
    ∘⊢ dist&

  -- under `&`
  dec-& : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
        → (Dec⟨ A ⟩ & Dec⟨ B ⟩) ⊢ Dec⟨ A & B ⟩
  dec-& A B =
    ⊕-E (⊕-E (dec-yes (A & B) ∘⊢ &-swap)
             (dec-no (A & B) ∘⊢ (¬G-map &-E₂ ∘⊢ &-E₁))
         ∘⊢ (dist& ∘⊢ &-swap))
        (dec-no (A & B) ∘⊢ (¬G-map &-E₁ ∘⊢ &-E₁))
    ∘⊢ dist&

  -- double negation introduction.  Named for its conclusion, like every
  -- other introduction rule here (`⊕-I₁`, `⇒-I`, `dec-yes`).
  ¬G¬G-I : (A : TheoryTy ℓA s) → A ⊢ ¬G ¬G A
  ¬G¬G-I A = ⇒-I (contra {A = A})

  -- DEPRECATED NAME.  `dni` is guessable only from the abbreviation, not
  -- from the statement; prefer `¬G¬G-I` in new code.
  dni : (A : TheoryTy ℓA s) → A ⊢ ¬G ¬G A
  dni = ¬G¬G-I

  -- and so the negation of a decided grammar is decided
  dec-¬ : (A : TheoryTy ℓA s) → Dec⟨ A ⟩ ⊢ Dec⟨ ¬G A ⟩
  dec-¬ A = ⊕-E (dec-no (¬G A) ∘⊢ ¬G¬G-I A) (dec-yes (¬G A))

  -- the units decide themselves
  dec-⊤ : ⊤G {s} ⊢ Dec⟨ ⊤G {s} ⟩
  dec-⊤ = dec-yes ⊤G

  dec-⊥ : ⊤G {s} ⊢ Dec⟨ ⊥G {s} ⟩
  dec-⊥ = dec-no ⊥G ∘⊢ ⇒-I &-E₂
