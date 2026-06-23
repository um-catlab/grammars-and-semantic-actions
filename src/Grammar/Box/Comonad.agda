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
open import Grammar.Box.Base Alphabet
open import Grammar.Box.Properties Alphabet
open import Grammar.Comonad.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓ : Level

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
  ; δ-nat = λ f → {!!}
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
