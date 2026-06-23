{- The guarded fixed point as a chain of □-coalgebra homomorphisms.

   Reading □-coalgebras as presheaves on the well-order of strings and
   □-coalgebra homomorphisms as natural transformations, this module shows
   that every arrow in the guarded fixed-point composite

        ⊤ --[ fix f ]--> A --[ a ]--> □ A --[ restrict ]--> ▷ A --[ f ]--> A

   is natural, i.e. a □-coalgebra homomorphism, and that the composite equals
   `fix f` (the Löb fixed point).  Concretely, given a box coalgebra (A , a)
   and a coalgebra hom f : (▷ A , ▷δ) → (A , a), we exhibit:

     ①  a        : (A , a)      → (□ A , δ)     -- FREE: this is `a`'s coassoc law
     ②  restrict : (□ A , δ)    → (▷ A , ▷δ)    -- naturality of √l-dist under
                                                    NonEmptyString ↪ String
     ③  f        : (▷ A , ▷δ)   → (A , a)        -- HYPOTHESIS
     ④  fix f    : (⊤ , γ⊤)     → (A , a)        -- Löb induction on the square

   The genuinely new content is the coaction `▷δ` on `▷ A` (the δ-formula with
   inner index restricted to nonempty strings) and the √l-dist reindexing lemma
   feeding ②.  The remaining holes are: the two coalgebra laws for `▷δ` and `γ⊤`
   (verbatim copies of the □-comonad proofs in Grammar.Box.Properties, with the
   index set restricted), the reindexing lemma, the Löb-unfolding equation, and
   the Löb naturality square. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Box.GuardedFixpoint (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.List.Properties using (¬cons≡nil)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Function Alphabet
open import Grammar.Top Alphabet
open import Grammar.Derivative.String Alphabet
open import Grammar.Box.Base Alphabet
open import Grammar.Box.Properties Alphabet
open import Grammar.Box.Comonad Alphabet
open import Grammar.Comonad.Base Alphabet
open import Grammar.Later.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓX ℓY : Level

--------------------------------------------------------------------------------
-- Nonempty concatenation: w ++ v is nonempty as soon as v is.
--------------------------------------------------------------------------------

++-ne : ∀ (w v : String) → (v ≡ [] → Empty.⊥) → w ++ v ≡ [] → Empty.⊥
++-ne []      v vne p = vne p
++-ne (x ∷ w) v vne p = ¬cons≡nil p

cat-ne : String → NonEmptyString → NonEmptyString
cat-ne w (v , vne) = (w ++ v) , ++-ne w v vne

--------------------------------------------------------------------------------
-- restrict : □ A ⊢ ▷ A   (drop the []-component; the iso □ A ≅ A & ▷ A makes
-- this π₂ and ε□ = √l-ε ∘ π₁).
--------------------------------------------------------------------------------

restrict : {A : Grammar ℓA} → □ A ⊢ ▷ A
restrict = &ᴰ-intro (λ w → π (w .fst))

--------------------------------------------------------------------------------
-- The coaction on ▷ A: the δ-formula with the inner &ᴰ ranging over nonempty
-- strings (and the outer projection of ▷ A taken at the nonempty string w++v).
--------------------------------------------------------------------------------

▷δ : {A : Grammar ℓA} → ▷ A ⊢ □ (▷ A)
▷δ {A = A} = &ᴰ-intro λ w →
  √l-dist {w = w}
  ∘g &ᴰ-intro λ v → √l-cat {A = A} {w = w} {v = v .fst} ∘g π (cat-ne w v)

-- γ⊤ : ⊤ ⊢ □ ⊤.  Each component ⊤ ⊢ √l-string w ⊤ is the unique such map,
-- here realised as ⇒-intro π₂ (√l-string w ⊤ = (⌈w⌉⊗⊤) ⇒ (⌈w⌉⊗⊤)).
γ⊤ : ⊤ ⊢ □ ⊤
γ⊤ = &ᴰ-intro (λ _ → ⇒-intro π₂)

--------------------------------------------------------------------------------
-- √l-string w preserves &ᴰ: √l-dist is one leg of the comparison iso
--      √l-string w (&[ x ∈ X ] B x)  ≅  &[ x ∈ X ] √l-string w (B x),
-- with inverse `&ᴰ-intro (λ x → √l-map (π x))`.  √w = (⌈w⌉⊗⊤) ⇒ (⌈w⌉⊗ -) is a
-- right adjoint, so it preserves the product &ᴰ and this is a genuine iso.
--------------------------------------------------------------------------------

-- Retract direction (FREE from √l-dist-proj + &ᴰ β/η).
√l-dist-retract :
  ∀ {X : Type ℓX} {B : X → Grammar ℓA} {w : String}
  → &ᴰ-intro (λ x → √l-map {w = w} (π x)) ∘g √l-dist {w = w} {B = B} ≡ id
√l-dist-retract {B = B} {w = w} =
  &ᴰ≡ _ _ (λ x → √l-dist-proj {B = B} {w = w} x)

-- Section direction (the other triangle: √w preserves the &ᴰ-product).  Proved
-- by the same `realign-√l`-is-the-identity (⌈⌉-uniqueness) argument as
-- √l-dist-proj, distributed over the whole family.
√l-dist-section :
  ∀ {X : Type ℓX} {B : X → Grammar ℓA} {w : String}
  → √l-dist {w = w} {B = B} ∘g &ᴰ-intro (λ x → √l-map {w = w} (π x)) ≡ id
√l-dist-section = {!!}

--------------------------------------------------------------------------------
-- The √l-dist reindexing lemma feeding step ②: distributing √l-string over a
-- &ᴰ commutes with reindexing the &ᴰ index along any ι.  Given the iso above
-- this is forced; we use both triangles to transport the (free) componentwise
-- agreement `r ∘ lhs ≡ reind` across √l-dist.
--------------------------------------------------------------------------------

√l-dist-reindex :
  ∀ {X : Type ℓX} {Y : Type ℓY} (ι : Y → X)
    {B : X → Grammar ℓA} {w : String}
  → √l-map {w = w} (&ᴰ-intro (λ y → π (ι y)))
      ∘g √l-dist {w = w} {B = B}
    ≡ √l-dist {w = w} {B = λ y → B (ι y)}
      ∘g &ᴰ-intro (λ y → π (ι y))
√l-dist-reindex {X = X} {Y = Y} ι {B = B} {w = w} =
  sym (cong (_∘g lhs) (√l-dist-section {B = λ y → B (ι y)} {w = w}))
  ∙ cong (√l-dist {w = w} {B = λ y → B (ι y)} ∘g_) r-lhs
  where
    -- the left-hand side, named so we can transport it across the iso
    lhs : (&[ x ∈ X ] √l-string w (B x)) ⊢ √l-string w (&[ y ∈ Y ] B (ι y))
    lhs = √l-map {w = w} (&ᴰ-intro (λ y → π (ι y))) ∘g √l-dist {w = w} {B = B}

    -- applying the retraction to `lhs` recovers the reindexing map (componentwise
    -- by √l-map functoriality + √l-dist-proj; both reductions are definitional)
    r-lhs : &ᴰ-intro (λ y → √l-map {w = w} (π y)) ∘g lhs
            ≡ &ᴰ-intro (λ y → π (ι y))
    r-lhs = &ᴰ≡ _ _ λ y →
      cong (_∘g √l-dist {w = w} {B = B})
           (sym (√l-map-seq {w = w} (&ᴰ-intro (λ y' → π (ι y'))) (π y)))
      ∙ √l-dist-proj {B = B} {w = w} (ι y)

--------------------------------------------------------------------------------
-- Fix a box coalgebra (A , a) at level ℓ-zero (so ⊤ and `lob` are available;
-- generalising to arbitrary ℓ needs ⊤* in place of ⊤).
--------------------------------------------------------------------------------

module _ (Acoalg : BoxCoalgebra {ℓ-zero}) where
  private
    A : Grammar ℓ-zero
    A = Acoalg .car
    a : A ⊢ □ A
    a = Acoalg .γ

  ------------------------------------------------------------------------------
  -- ▷ A and ⊤ as box coalgebras.
  ------------------------------------------------------------------------------

  ▷-coalg : BoxCoalgebra {ℓ-zero}
  ▷-coalg .car = ▷ A
  ▷-coalg .γ   = ▷δ
  ▷-coalg .counit-coh  = {!!}   -- copy of □-counit-l, inner index = NonEmptyString
  ▷-coalg .coassoc-coh = {!!}   -- copy of □-coassoc, inner index = NonEmptyString

  ⊤-coalg : BoxCoalgebra {ℓ-zero}
  ⊤-coalg .car = ⊤
  ⊤-coalg .γ   = γ⊤
  ⊤-coalg .counit-coh  = {!!}   -- unique into ⊤; √l-string w ⊤ is contractible
  ⊤-coalg .coassoc-coh = {!!}

  ------------------------------------------------------------------------------
  -- ① a is a coalgebra hom (A , a) → (□ A , δ).  FREE: the square
  --        map□ a ∘g a ≡ δ ∘g a
  -- is exactly the (symmetric) coassociativity law of the coalgebra (A , a).
  ------------------------------------------------------------------------------

  a-hom : BoxCoalgebraHom Acoalg (cofree-box A)
  a-hom .hom  = a
  a-hom .comm = sym (Acoalg .coassoc-coh)

  ------------------------------------------------------------------------------
  -- ② restrict is a coalgebra hom (□ A , δ) → (▷ A , ▷δ).  Per outer index w,
  -- both sides reduce to √l-dist ∘ (reindexed √l-cat tower); they agree by
  -- `√l-dist-reindex` for ι = (NonEmptyString → String, fst).
  ------------------------------------------------------------------------------

  restrict-hom : BoxCoalgebraHom (cofree-box A) ▷-coalg
  restrict-hom .hom  = restrict
  restrict-hom .comm = &ᴰ≡ _ _ λ w →
    -- Per outer index w both sides are √l-dist ∘ (√l-cat tower); after the
    -- definitional reductions of δ, ▷δ, map□, restrict they differ only by
    -- whether the NonEmptyString ↪ String reindexing sits inside or outside
    -- √l-dist.  That is exactly `√l-dist-reindex fst`.
    cong (_∘g Gfam w)
      (√l-dist-reindex {X = String} {Y = NonEmptyString}
        fst {B = λ u → √l-string u A} {w = w})
    where
      -- π w ∘g δ = √l-dist ∘g Gfam w  (definitionally)
      Gfam : (w : String) → □ A ⊢ &[ u ∈ String ] √l-string w (√l-string u A)
      Gfam w = &ᴰ-intro λ u →
        √l-cat {A = A} {w = w} {v = u} ∘g π {A = λ z → √l-string z A} (w ++ u)

  ------------------------------------------------------------------------------
  -- ③ + ④: given f a coalgebra hom (▷ A , ▷δ) → (A , a), assemble the endo
  -- coalgebra hom Φ = f ∘ restrict ∘ a and take its Löb fixed point.
  ------------------------------------------------------------------------------

  module _ (f : BoxCoalgebraHom ▷-coalg Acoalg) where
    -- The composite endomorphism of (A , a) whose Löb fixed point we take.
    Φ : BoxCoalgebraHom Acoalg Acoalg
    Φ = compCoalgebraHom □-Comonad f
          (compCoalgebraHom □-Comonad restrict-hom a-hom)

    -- The fixed point on underlying grammars.
    fix : ⊤ ⊢ A
    fix = lob (f .hom)

    -- The user's defining equation: the four-step composite equals fix.
    --        ⊤ -[fix]-> A -[a]-> □A -[restrict]-> ▷A -[f]-> A   =   fix
    -- (restrict ∘g a is the presheaf "next"; this is the Löb unfolding lemma,
    --  not yet available in Grammar.Later.Base.)
    fix-eq : f .hom ∘g restrict ∘g a ∘g fix ≡ fix
    fix-eq = {!!}

    -- ④ fix is a coalgebra hom (⊤ , γ⊤) → (A , a): the square
    --        map□ fix ∘g γ⊤ ≡ a ∘g fix
    -- holds by Löb induction (the square at u depends only on shorter strings,
    -- and Φ being a coalgebra endo-hom makes the inductive step type-check).
    fix-hom : BoxCoalgebraHom ⊤-coalg Acoalg
    fix-hom .hom  = fix
    fix-hom .comm = {!!}
