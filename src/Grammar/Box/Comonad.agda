{- The box modality □ packaged as a (semantic) comonad, and the resulting
   characterisation of "box coalgebras".

   □ is the "all suffixes" comonad: □ A (u) ≅ ∏_{r a suffix of u} A r, with
   counit ε□ reading off the full-string suffix and comultiplication δ. It is
   a genuine covariant endofunctor (witnessed by map□) but is NOT in the image
   of the `Functor` syntactic codes — its definition goes through the
   cartesian arrow ⇒. So box coalgebras are precisely the coalgebras of this
   comonad, which we set up via the *semantic* comonad of Grammar.Comonad.Base. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Box.Comonad (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.Product Alphabet
open import Grammar.Derivative.String Alphabet
open import Grammar.Box.Base Alphabet
open import Grammar.Box.Properties Alphabet
open import Grammar.Comonad.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓ ℓA ℓB ℓX : Level

--------------------------------------------------------------------------------
-- Naturality of the building blocks of δ
--
-- `√l-cat-nat` (naturality of √l-cat) lives in Grammar.Box.Properties — it needs
-- the opaque pointwise unfolding. `√l-dist-nat` is algebraic (the √l-dist iso),
-- proved here.
--------------------------------------------------------------------------------

-- √l-string w preserves &ᴰ via √l-dist, naturally in the family.
√l-dist-nat : ∀ {w : String} {X : Type ℓX} {B C : X → Grammar ℓA}
  (g : ∀ x → B x ⊢ C x)
  → √l-map {w = w} (&ᴰ-intro (λ x → g x ∘g π x)) ∘g √l-dist {w = w} {B = B}
    ≡ √l-dist {w = w} {B = C} ∘g &ᴰ-intro (λ x → √l-map {w = w} (g x) ∘g π x)
-- Transport the (free, componentwise) agreement `r ∘ lhs ≡ rhs-family` across
-- the √l-string w (&ᴰ) ≅ &ᴰ (√l-string w) iso (retract `√l-dist-proj` + section
-- `√l-dist-section`), exactly as in √l-dist-reindex.
√l-dist-nat {w = w} {X = X} {B = B} {C = C} g =
  sym (cong (_∘g lhs) (√l-dist-section {B = C} {w = w}))
  ∙ cong (√l-dist {w = w} {B = C} ∘g_) r-lhs
  where
    lhs : (&[ x ∈ X ] √l-string w (B x)) ⊢ √l-string w (&[ x ∈ X ] C x)
    lhs = √l-map {w = w} (&ᴰ-intro (λ x → g x ∘g π x)) ∘g √l-dist {w = w} {B = B}

    r-lhs : &ᴰ-intro (λ x → √l-map {w = w} (π x)) ∘g lhs
            ≡ &ᴰ-intro (λ x → √l-map {w = w} (g x) ∘g π x)
    r-lhs = &ᴰ≡ _ _ λ x →
      cong (_∘g √l-dist {w = w} {B = B})
        (sym (√l-map-seq {w = w} (&ᴰ-intro (λ x' → g x' ∘g π x')) (π x)))
      ∙ cong (_∘g √l-dist {w = w} {B = B}) (√l-map-seq {w = w} (π x) (g x))
      ∙ cong (√l-map {w = w} (g x) ∘g_) (√l-dist-proj {B = B} {w = w} x)

-- δ naturality, assembled from the two lemmas above. The &ᴰ/π β-laws used
-- below are all definitional (π and &ᴰ-intro are not opaque), so each `cong`
-- step lands on the next on the nose.
□-δ-nat : {A B : Grammar ℓ} (f : A ⊢ B)
  → δ ∘g map□ f ≡ map□ (map□ f) ∘g δ
□-δ-nat {A = A} {B = B} f = &ᴰ≡ _ _ λ w → δ-nat-w w
  where
    -- the inner δ-slot family `&[v] √w (√v -)`, polymorphic in the grammar:
    -- the LHS of δ-nat-w uses it at B (codomain of `map□ f`), the RHS at A.
    K : ∀ {ℓ'} {A' : Grammar ℓ'} w
      → □ A' ⊢ &[ v ∈ String ] √l-string w (√l-string v A')
    K w = &ᴰ-intro (λ v → √l-cat {w = w} {v = v} ∘g π (w ++ v))
    δ-nat-w : ∀ w
      → (√l-dist {w = w} ∘g K {A' = B} w) ∘g map□ f
        ≡ √l-map {w = w} (map□ f) ∘g (√l-dist {w = w} ∘g K {A' = A} w)
    δ-nat-w w =
      -- rewrite each v-slot of the family by √l-cat naturality …
      cong (√l-dist {w = w} ∘g_)
        (&ᴰ≡ _ _ (λ v → cong (_∘g π (w ++ v)) (√l-cat-nat {w = w} {v = v} f)))
      -- … then pull √l-map (map□ f) back out through √l-dist.
      ∙ cong (_∘g K {A' = A} w) (sym (√l-dist-nat {w = w} (λ v → √l-map {w = v} f)))

--------------------------------------------------------------------------------
-- □ as a comonad
--------------------------------------------------------------------------------

□-Comonad : Comonad ℓ
□-Comonad = record
  { F₀ = □_
  ; F₁ = map□
  ; F-id = map□-id
  ; F-seq = map□-seq
  ; ε = ε□
  ; δ = δ
  ; ε-nat = λ f → cong (_∘g π []) (√l-ε-nat f)
                  -- ε□ ∘g map□ f reduces (π/&ᴰ-intro β) to (√l-ε ∘g √l-map[] f) ∘g π []
  ; δ-nat = □-δ-nat
  ; counit-l = □-counit-l
  ; counit-r = □-counit-r   -- still a hole in Grammar.Box.Properties
  ; coassoc = □-coassoc     -- still a hole in Grammar.Box.Properties
  }

--------------------------------------------------------------------------------
-- Box coalgebras
--------------------------------------------------------------------------------

-- A box coalgebra is exactly a coalgebra for the □ comonad.
BoxCoalgebra : Type (ℓ-suc ℓ)
BoxCoalgebra {ℓ} = Coalgebra (□-Comonad {ℓ})

BoxCoalgebraHom : BoxCoalgebra {ℓ} → BoxCoalgebra {ℓ} → Type ℓ
BoxCoalgebraHom = CoalgebraHom □-Comonad

-- The cofree box coalgebra on A is (□ A , δ). These are the "genuine boxes":
-- by the adjunction below, box-coalgebra maps into (□ A , δ) are the same as
-- plain grammar maps into A.
cofree-box : Grammar ℓ → BoxCoalgebra {ℓ}
cofree-box = cofree □-Comonad

-- Characterisation (cofree adjunction): forgetful ⊣ cofree, i.e.
--     BoxCoalgebraHom X (cofree-box A)  ≅  (X .car ⊢ A).
-- `cofree-transpose`/`cofree-transpose⁻` and the triangle `cofree-β` are
-- inherited from Grammar.Comonad.Base.

--------------------------------------------------------------------------------
-- The final box coalgebra
--------------------------------------------------------------------------------

-- The terminal box coalgebra is the cofree coalgebra on the terminal grammar,
-- (□ ⊤* , δ). Since □ preserves the terminal object (□ ⊤* ≅ ⊤*, because each
-- √l-string w ⊤* is a contractible "prop ⇒ prop"), this collapses to the
-- trivial coalgebra on ⊤* — matching the earlier observation that the final
-- box coalgebra carries no information.
terminalBoxCoalgebra : BoxCoalgebra {ℓ}
terminalBoxCoalgebra {ℓ} = cofree-box (⊤* {ℓ})

-- The universal map: every box coalgebra has a (unique) map to the terminal
-- one, namely the cofree transpose of the unique map into ⊤*.
toTerminal : (X : BoxCoalgebra {ℓ}) → BoxCoalgebraHom X terminalBoxCoalgebra
toTerminal X = cofree-transpose □-Comonad {X = X} ⊤*-intro

-- Uniqueness: any two box-coalgebra maps into terminalBoxCoalgebra agree.
-- Via the cofree adjunction their transposes are maps X .car ⊢ ⊤*, which are
-- unique by `is-terminal-⊤*`.
toTerminalUnique : (X : BoxCoalgebra {ℓ})
  → (h : BoxCoalgebraHom X terminalBoxCoalgebra) → h .hom ≡ toTerminal X .hom
toTerminalUnique X h =
  -- h.hom ≡ cofree-transpose (cofree-transpose⁻ h), and cofree-transpose⁻ h is
  -- a map into ⊤*, hence equal to ⊤*-intro by terminality.
  sym (cofree-η □-Comonad h)
  ∙ cong (λ g → cofree-transpose □-Comonad {X = X} g .hom)
      ( sym (is-terminal-⊤* .snd (cofree-transpose⁻ □-Comonad h))
        ∙ is-terminal-⊤* .snd ⊤*-intro )
