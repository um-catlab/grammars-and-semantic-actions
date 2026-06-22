open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Derivative.Disjunction (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Top Alphabet
open import Grammar.String Alphabet
open import Grammar.Derivative.Base Alphabet
open import Grammar.Inductive.Functor Alphabet
import Grammar.Derivative.String Alphabet as DString
open import Term.Base Alphabet

private
  variable
    w : String
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

data √l-tag : Type where
  prefix nah : √l-tag

¬Start : String → Grammar ℓ-zero
¬Start w = {!!}

√l-string-F' : String → Functor Unit
√l-string-F' w = ⊕e √l-tag λ { prefix → k ⌈ w ⌉ ⊗e Var _ ; nah → k (¬Start w)}

-- We want coalgebras for this functor
√l-string-F : Functor Unit
√l-string-F = &e String √l-string-F'

-- -- String-indexed Brzozowski derivatives.
-- Dr-string : String → Grammar ℓA → Grammar ℓA
-- Dr-string w A = ⌈ w ⌉ ⊸ A

-- Dl-string : Grammar ℓA → String → Grammar ℓA
-- Dl-string A w = A ⟜ ⌈ w ⌉

-- √l-string : String → Grammar ℓA → Grammar ℓA
-- √l-string w A = {!!}
-- (⌈ w ⌉ ⊗ ⊤) ⇒ (⌈ w ⌉ ⊗ A)

-- √r-string : String → Grammar ℓA → Grammar ℓA
-- √r-string w A = (⊤ ⊗ ⌈ w ⌉) ⇒ (A ⊗ ⌈ w ⌉)

-- opaque
--   unfolding _⟜_ _⇒_ _⊗_ ⊤
--   √l-string-app : Dl-string (√l-string w A) w ⊢ A
--   √l-string-app {w = w} {A = A} w' d =
--     Eq.transport A uniq-suffix (step .snd .snd)
--     where
--       step : (⌈ w ⌉ ⊗ A) (w ++ w')
--       step = d w (mk⌈⌉ w) (((w , w') , Eq.refl) , (mk⌈⌉ w , _))

--       uniq-suffix : step .fst .fst .snd Eq.≡ w'
--       uniq-suffix =
--         ++-cancelˡEq w
--           (Eq.sym
--             (Eq.transport (λ ww → w ++ w' Eq.≡ ww ++ step .fst .fst .snd)
--                           (Eq.sym (uniquely-supported-⌈⌉Eq w (step .fst .fst .fst)
--                                     (step .snd .fst)))
--                           (step .fst .snd)))

--   √r-string-app : Dr-string w (√r-string w A) ⊢ A
--   √r-string-app {w = w} {A = A} w' d =
--     Eq.transport A uniq-prefix (step .snd .fst)
--     where
--       step : (A ⊗ ⌈ w ⌉) (w' ++ w)
--       step = d w (mk⌈⌉ w) (((w' , w) , Eq.refl) , (_ , mk⌈⌉ w))

--       uniq-prefix : step .fst .fst .fst Eq.≡ w'
--       uniq-prefix =
--         ++-cancelʳEq w
--           (Eq.sym
--             (Eq.transport (λ ww → w' ++ w Eq.≡ step .fst .fst .fst ++ ww)
--                           (Eq.sym (uniquely-supported-⌈⌉Eq w (step .fst .fst .snd)
--                                     (step .snd .snd)))
--                           (step .fst .snd)))

--   -- Composition of amazing right adjoints: peeling a `w ++ v`-prefix in
--   -- one go is the same as peeling `w` and then peeling `v` off the
--   -- residual. This is the coassociativity step of the □-comonad.
--   --
--   -- Pointwise, the outer `⌈ w ⌉ ⊗ ⊤` fixes the split `u = w' ++ rest`,
--   -- the inner `⌈ v ⌉ ⊗ ⊤` fixes `rest = v' ++ rest2`; recombining
--   -- `⌈ w ⌉ ⊗ ⌈ v ⌉` into `⌈ w ++ v ⌉` (via `⌈⌉-++`) feeds the original
--   -- `w ++ v`-peel, whose `A`-output lands on `rest2` by uniqueness of
--   -- the `⌈ w ++ v ⌉`-prefix.
--   √l-cat :
--     ∀ {ℓA} {A : Grammar ℓA} {w v : String} →
--     √l-string (w ++ v) A ⊢ √l-string w (√l-string v A)
--   √l-cat {A = A} {w = w} {v = v} u d pw =
--     pw .fst , (pw .snd .fst , innerfn)
--     where
--       w' rest : String
--       w'   = pw .fst .fst .fst
--       rest = pw .fst .fst .snd

--       ⌈w⌉w' : ⌈ w ⌉ w'
--       ⌈w⌉w' = pw .snd .fst

--       w≡w' : w Eq.≡ w'
--       w≡w' = uniquely-supported-⌈⌉Eq w w' ⌈w⌉w'

--       innerfn : √l-string v A rest
--       innerfn pv =
--         pv .fst , (pv .snd .fst , Eq.transport A ra≡rest2 (da .snd .snd))
--         where
--           v' rest2 : String
--           v'    = pv .fst .fst .fst
--           rest2 = pv .fst .fst .snd

--           ⌈v⌉v' : ⌈ v ⌉ v'
--           ⌈v⌉v' = pv .snd .fst

--           v≡v' : v Eq.≡ v'
--           v≡v' = uniquely-supported-⌈⌉Eq v v' ⌈v⌉v'

--           -- u = w' ++ rest = w' ++ (v' ++ rest2) = (w' ++ v') ++ rest2
--           u≡w'v'rest2 : u Eq.≡ (w' ++ v') ++ rest2
--           u≡w'v'rest2 =
--             pw .fst .snd
--             Eq.∙ Eq.ap (w' ++_) (pv .fst .snd)
--             Eq.∙ Eq.sym (++-assoc-Eq w' v' rest2)

--           ⌈wv⌉ : ⌈ w ++ v ⌉ (w' ++ v')
--           ⌈wv⌉ =
--             ⌈⌉-++ w v (w' ++ v')
--               (((w' , v') , Eq.refl) , (⌈w⌉w' , ⌈v⌉v'))

--           da : (⌈ w ++ v ⌉ ⊗ A) u
--           da = d (((w' ++ v' , rest2) , u≡w'v'rest2) , (⌈wv⌉ , _))

--           -- the peel lands its `⌈ w ++ v ⌉`-prefix on `w' ++ v'` ...
--           la≡w'v' : da .fst .fst .fst Eq.≡ w' ++ v'
--           la≡w'v' =
--             Eq.sym
--               (uniquely-supported-⌈⌉Eq (w ++ v) (da .fst .fst .fst)
--                 (da .snd .fst))
--             Eq.∙ Eq.ap (_++ v) w≡w'
--             Eq.∙ Eq.ap (w' ++_) v≡v'

--           -- ... hence its `A`-output is on `rest2`.
--           ra≡rest2 : da .fst .fst .snd Eq.≡ rest2
--           ra≡rest2 =
--             ++-cancelˡEq (w' ++ v')
--               (Eq.ap (_++ da .fst .fst .snd) (Eq.sym la≡w'v')
--                Eq.∙ Eq.sym (da .fst .snd)
--                Eq.∙ u≡w'v'rest2)

-- √l-ε : √l-string [] A ⊢ A
-- √l-ε = ⊗-unit-l ∘g ⇒-app ∘g &-intro id (⊗-unit-l⁻ ∘g ⊤-intro)

-- √l-ε⁻ : A ⊢ √l-string [] A
-- √l-ε⁻ = ⇒-intro (⊗-unit-l⁻ ∘g π₁)

-- -- Functor action of √l-string w (in its grammar argument).
-- √l-map : A ⊢ B → √l-string w A ⊢ √l-string w B
-- √l-map f = ⇒-intro ((id ,⊗ f) ∘g ⇒-app)

-- √r-ε : √r-string [] A ⊢ A
-- √r-ε = ⊗-unit-r ∘g ⇒-app ∘g &-intro id (⊗-unit-r⁻ ∘g ⊤-intro)

-- √r-ε⁻ : A ⊢ √r-string [] A
-- √r-ε⁻ = ⇒-intro (⊗-unit-r⁻ ∘g π₁)
