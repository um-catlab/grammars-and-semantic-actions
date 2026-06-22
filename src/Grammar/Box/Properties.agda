open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Box.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality using (eqToPath)

open import Grammar.Base Alphabet
open import Grammar.Derivative.String Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.String Alphabet
open import Grammar.Top Alphabet
open import Grammar.Box.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC

-- Bridge: Eq.transport along p is the cubical transport-filler over eqToPath p.
eqTransportFiller :
  ∀ {ℓ ℓ'} {X : Type ℓ} {a b : X} (P : X → Type ℓ')
  → (p : a Eq.≡ b) (x : P a)
  → PathP (λ i → P (eqToPath p i)) x (Eq.transport P p x)
eqTransportFiller P Eq.refl x = refl

-- The endofunctor action of □ on morphisms.
map□ : A ⊢ B → □ A ⊢ □ B
map□ f = &ᴰ-intro λ w → √l-map {w = w} f ∘g π w

--------------------------------------------------------------------------------
-- Functoriality of √l-string w  (reusable categorical lemmas)
--------------------------------------------------------------------------------

private
  -- ⇒-intro ⇒-app ≡ id (one half of the ⇒ adjunction's η/β, repackaged)
  ⇒-app≡intro⁻id : ∀ {ℓP ℓQ} {P : Grammar ℓP} {Q : Grammar ℓQ}
    → ⇒-app {A = P} {B = Q} ≡ ⇒-intro⁻ id
  ⇒-app≡intro⁻id = cong (⇒-app ∘g_) (sym (&-η id))

  opaque
    unfolding _⇒_ _&_ ⇒-intro ⇒-app &-intro π₁ π₂
    -- precomposition pushes through ⇒-intro
    ⇒-intro-precomp : ∀ {ℓP ℓQ ℓR ℓS}
      {P : Grammar ℓP} {Q : Grammar ℓQ} {R : Grammar ℓR} {S : Grammar ℓS}
      (e : Q & R ⊢ S) (h : P ⊢ Q)
      → ⇒-intro e ∘g h ≡ ⇒-intro (e ∘g (h ,&p id))
    ⇒-intro-precomp e h = refl

    -- β for ⇒-app applied to a forked (⇒-intro e , m)
    ⇒-app-fork : ∀ {ℓP ℓQ ℓR}
      {P : Grammar ℓP} {Q : Grammar ℓQ} {R : Grammar ℓR}
      (e : R & P ⊢ Q) (m : R ⊢ P)
      → ⇒-app ∘g &-intro (⇒-intro e) m ≡ e ∘g &-intro id m
    ⇒-app-fork e m = refl

    -- &-intro commutes with precomposition
    &-intro∘g : ∀ {ℓP ℓQ ℓR ℓS}
      {P : Grammar ℓP} {Q : Grammar ℓQ} {R : Grammar ℓR} {S : Grammar ℓS}
      (a : R ⊢ P) (b : R ⊢ Q) (h : S ⊢ R)
      → &-intro a b ∘g h ≡ &-intro (a ∘g h) (b ∘g h)
    &-intro∘g a b h = refl

√l-map-id : ∀ {w} → √l-map {w = w} (id {A = A}) ≡ id {A = √l-string w A}
√l-map-id {A = A} {w = w} =
  cong (λ z → ⇒-intro (z ∘g ⇒-app)) (id,⊗id≡id {A = ⌈ w ⌉} {B = A})
  ∙ cong ⇒-intro ⇒-app≡intro⁻id
  ∙ ⇒-η id

√l-map-seq : ∀ {w} (f : A ⊢ B) (g : B ⊢ C)
  → √l-map {w = w} (g ∘g f) ≡ √l-map {w = w} g ∘g √l-map {w = w} f
√l-map-seq {A = A} {B = B} {C = C} {w = w} f g = sym (p1 ∙ p2)
  where
    eg : √l-string w B & (⌈ w ⌉ ⊗ ⊤) ⊢ (⌈ w ⌉ ⊗ C)
    eg = (id ,⊗ g) ∘g ⇒-app
    ef : √l-string w A & (⌈ w ⌉ ⊗ ⊤) ⊢ (⌈ w ⌉ ⊗ B)
    ef = (id ,⊗ f) ∘g ⇒-app
    p1 : √l-map {w = w} g ∘g √l-map {w = w} f
       ≡ ⇒-intro (eg ∘g (√l-map {w = w} f ,&p id))
    p1 = ⇒-intro-precomp eg (√l-map {w = w} f)
    p2 : ⇒-intro (eg ∘g (√l-map {w = w} f ,&p id)) ≡ √l-map {w = w} (g ∘g f)
    p2 =
      cong ⇒-intro
        ( cong ((id ,⊗ g) ∘g_) (⇒-β ef)
        ∙ cong (_∘g ⇒-app) ⊗-intro⊗-intro )

map□-id : map□ (id {A = A}) ≡ id
map□-id = &ᴰ≡ _ _ λ w → cong (_∘g π w) (√l-map-id {w = w})

map□-seq : (f : A ⊢ B) (g : B ⊢ C) → map□ (g ∘g f) ≡ map□ g ∘g map□ f
map□-seq f g = &ᴰ≡ _ _ λ w → cong (_∘g π w) (√l-map-seq {w = w} f g)

--------------------------------------------------------------------------------
-- Coherences feeding the comonad laws
--------------------------------------------------------------------------------

-- naturality of the counit √l-ε
√l-ε-nat : (f : A ⊢ B) → f ∘g √l-ε ≡ √l-ε ∘g √l-map {w = []} f
√l-ε-nat {A = A} {B = B} f = sym nat
  where
    e : √l-string [] A & (⌈ [] ⌉ ⊗ ⊤) ⊢ (⌈ [] ⌉ ⊗ B)
    e = (id ,⊗ f) ∘g ⇒-app
    ⊤u : ⊤-intro ∘g √l-map {w = []} f ≡ ⊤-intro
    ⊤u =
      sym (is-terminal-⊤ .snd (⊤-intro ∘g √l-map {w = []} f))
      ∙ is-terminal-⊤ .snd ⊤-intro
    nat : √l-ε ∘g √l-map {w = []} f ≡ f ∘g √l-ε
    nat =
      cong (λ z → ⊗-unit-l ∘g ⇒-app ∘g z)
           (&-intro∘g id (⊗-unit-l⁻ ∘g ⊤-intro) (√l-map {w = []} f))
      ∙ cong (⊗-unit-l ∘g_)
           (⇒-app-fork e ((⊗-unit-l⁻ ∘g ⊤-intro) ∘g √l-map {w = []} f))
      ∙ cong (λ z → ⊗-unit-l ∘g e ∘g &-intro id z) (cong (⊗-unit-l⁻ ∘g_) ⊤u)
      ∙ cong (_∘g (⇒-app ∘g &-intro id (⊗-unit-l⁻ ∘g ⊤-intro)))
           (sym (⊗-unit-l⊗-intro f))

-- projecting a component after √l-dist is the same as projecting it first.
-- Pointwise: the left side is the x-component of the box (= π x u F pw)
-- realigned onto pw's ⌈ w ⌉-split; that realignment is the identity by
-- ⌈ w ⌉-uniqueness (matching ⌈⌉-⊗&ᴰ-distL⁻Eq's own 12≡-Eq).
opaque
  unfolding ⌈⌉-⊗&ᴰ-distL⁻Eq _⇒_ ⇒-app ⇒-intro _⊗_ ⊗-intro _&_ &-intro π₁ π₂
            uniquely-supported-⌈⌉Eq same-parses the-split
  √l-dist-proj-pt :
    ∀ {ℓX} {X : Type ℓX} {B : X → Grammar ℓA} {w} (x : X)
      (u : String) (F : (&[ y ∈ X ] √l-string w (B y)) u)
    → (√l-map {w = w} (π x) ∘g √l-dist {w = w} {B = B}) u F ≡ π x u F
  √l-dist-proj-pt {B = B} {w = w} x u F = funExt λ pw →
    let
      famx : (⌈ w ⌉ ⊗ B x) u
      famx = π x u F pw

      12≡ : famx .fst .fst .snd Eq.≡ pw .fst .fst .snd
      12≡ = ++-cancelˡEq (pw .fst .fst .fst)
        ( Eq.ap (_++ famx .fst .fst .snd)
            ( Eq.sym (uniquely-supported-⌈⌉Eq w (pw .fst .fst .fst) (pw .snd .fst))
              Eq.∙ uniquely-supported-⌈⌉Eq w (famx .fst .fst .fst) (famx .snd .fst))
          Eq.∙ Eq.sym (famx .fst .snd)
          Eq.∙ pw .fst .snd )

      lp : pw .fst .fst .fst ≡ famx .fst .fst .fst
      lp = eqToPath
        ( Eq.sym (uniquely-supported-⌈⌉Eq w (pw .fst .fst .fst) (pw .snd .fst))
          Eq.∙ uniquely-supported-⌈⌉Eq w (famx .fst .fst .fst) (famx .snd .fst))

      rp : pw .fst .fst .snd ≡ famx .fst .fst .snd
      rp = sym (eqToPath 12≡)

      sp≡ : pw .fst .fst ≡ famx .fst .fst
      sp≡ = λ i → lp i , rp i

      pp : PathP (λ i → ⌈ w ⌉ (sp≡ i .fst) × B x (sp≡ i .snd))
                 (pw .snd .fst , Eq.transport (B x) 12≡ (famx .snd .snd))
                 (famx .snd)
      pp = ΣPathP
        ( isProp→PathP (λ i → isLang⌈⌉ w (lp i)) _ _
        , symP (eqTransportFiller (B x) 12≡ (famx .snd .snd)) )
    in ⊗≡ {A = ⌈ w ⌉} {B = B x} _ _ sp≡ pp

  √l-dist-proj : ∀ {ℓX} {X : Type ℓX} {B : X → Grammar ℓA} {w} (x : X)
    → √l-map {w = w} (π x) ∘g √l-dist {w = w} {B = B} ≡ π x
  √l-dist-proj {B = B} {w = w} x =
    funExt λ u → funExt λ F → √l-dist-proj-pt x u F

-- √l-ε and √l-ε⁻ are inverse on √l-string [] (algebraic).
√l-εε⁻ : √l-ε ∘g √l-ε⁻ ≡ id {A = A}
√l-εε⁻ {A = A} =
  cong (λ z → ⊗-unit-l ∘g ⇒-app ∘g z)
       (&-intro∘g id (⊗-unit-l⁻ ∘g ⊤-intro) √l-ε⁻)
  ∙ cong (⊗-unit-l ∘g_)
       (⇒-app-fork (⊗-unit-l⁻ ∘g π₁) ((⊗-unit-l⁻ ∘g ⊤-intro) ∘g √l-ε⁻))
  ∙ cong (λ z → ⊗-unit-l ∘g ⊗-unit-l⁻ ∘g z)
       (&-β₁ id ((⊗-unit-l⁻ ∘g ⊤-intro) ∘g √l-ε⁻))
  ∙ ⊗-unit-l⁻l

-- peeling [] (via √l-ε) undoes a √l-cat at depth [].
opaque
  unfolding √l-cat _⇒_ ⇒-app ⇒-intro _⊗_ ⊗-intro ⊤ ⊤-intro ⊗-unit-l ⊗-unit-l⁻
            &-intro ε ε-intro uniquely-supported-⌈⌉Eq same-parses the-split
  √l-cat-ε-pt :
    ∀ {ℓA} {A : Grammar ℓA} {v : String}
      (u : String) (d : √l-string v A u)
    → (√l-ε ∘g √l-cat {A = A} {w = []} {v = v}) u d ≡ d
  √l-cat-ε-pt {A = A} {v = v} u d = funExt λ pv →
    let
      v' : String
      v'    = pv .fst .fst .fst
      rest2 : String
      rest2 = pv .fst .fst .snd

      v≡v' : v Eq.≡ v'
      v≡v' = uniquely-supported-⌈⌉Eq v v' (pv .snd .fst)

      u≡v'rest2 : u Eq.≡ ([] ++ v') ++ rest2
      u≡v'rest2 =
        Eq.refl
        Eq.∙ Eq.ap ([] ++_) (pv .fst .snd)
        Eq.∙ Eq.sym (++-assoc-Eq [] v' rest2)

      ⌈wv⌉ : ⌈ [] ++ v ⌉ ([] ++ v')
      ⌈wv⌉ = ⌈⌉-++ [] v ([] ++ v')
               ((([] , v') , Eq.refl) , (ε-intro , pv .snd .fst))

      input : (⌈ v ⌉ ⊗ ⊤) u
      input = ((([] ++ v' , rest2) , u≡v'rest2) , (⌈wv⌉ , _))

      da : (⌈ v ⌉ ⊗ A) u
      da = d input

      la≡v' : da .fst .fst .fst Eq.≡ [] ++ v'
      la≡v' =
        Eq.sym
          (uniquely-supported-⌈⌉Eq ([] ++ v) (da .fst .fst .fst) (da .snd .fst))
        Eq.∙ Eq.ap (_++ v) (uniquely-supported-⌈⌉Eq [] [] ε-intro)
        Eq.∙ Eq.ap ([] ++_) v≡v'

      ra≡rest2 : da .fst .fst .snd Eq.≡ rest2
      ra≡rest2 =
        ++-cancelˡEq ([] ++ v')
          (Eq.ap (_++ da .fst .fst .snd) (Eq.sym la≡v')
           Eq.∙ Eq.sym (da .fst .snd)
           Eq.∙ u≡v'rest2)

      inp≡pv : input ≡ pv
      inp≡pv = ⊗≡ {A = ⌈ v ⌉} {B = ⊤} input pv refl
        (ΣPathP (isLang⌈⌉ v v' ⌈wv⌉ (pv .snd .fst) , isPropUnit _ _))

      Pd : da ≡ d pv
      Pd = cong d inp≡pv

      lp : v' ≡ d pv .fst .fst .fst
      lp = sym (eqToPath la≡v') ∙ cong (λ z → z .fst .fst .fst) Pd

      rp : rest2 ≡ d pv .fst .fst .snd
      rp = sym (eqToPath ra≡rest2) ∙ cong (λ z → z .fst .fst .snd) Pd

      sp≡ : pv .fst .fst ≡ d pv .fst .fst
      sp≡ = λ i → lp i , rp i

      pp : PathP (λ i → ⌈ v ⌉ (sp≡ i .fst) × A (sp≡ i .snd))
                 (pv .snd .fst , Eq.transport A ra≡rest2 (da .snd .snd))
                 (d pv .snd)
      pp = ΣPathP
        ( isProp→PathP (λ i → isLang⌈⌉ v (lp i)) _ _
        , compPathP' {B = A}
            (symP (eqTransportFiller A ra≡rest2 (da .snd .snd)))
            (λ i → Pd i .snd .snd) )
    in ⊗≡ {A = ⌈ v ⌉} {B = A} _ _ sp≡ pp

  √l-cat-ε : ∀ {v} → √l-ε ∘g √l-cat {A = A} {w = []} {v = v} ≡ id
  √l-cat-ε {A = A} {v = v} =
    funExt λ u → funExt λ d → √l-cat-ε-pt {A = A} {v = v} u d

--------------------------------------------------------------------------------
-- Comonad laws
--------------------------------------------------------------------------------

-- left counit:  ε□ ∘g δ ≡ id
-- Per component v:
--   π v ∘ ε□ ∘ δ
--     = π v ∘ √l-ε ∘ √l-dist[] ∘ (λ v'. √l-cat[]v' ∘ π v')   [δ at []]
--     = √l-ε ∘ √l-map (π v) ∘ √l-dist[] ∘ (...)               [√l-ε-nat]
--     = √l-ε ∘ π v ∘ (...)                                    [√l-dist-proj]
--     = √l-ε ∘ √l-cat[]v ∘ π v                                [&ᴰ β, [] ++ v = v]
--     = π v                                                   [√l-cat-ε]
□-counit-l : ε□ ∘g δ ≡ id {A = □ A}
□-counit-l {A = A} = &ᴰ≡ _ _ λ v →
  cong (_∘g (√l-dist {w = []} ∘g &ᴰ-intro (λ v' → √l-cat {w = []} {v = v'} ∘g π v')))
       (√l-ε-nat (π v))
  ∙ cong (λ z → √l-ε ∘g z ∘g &ᴰ-intro (λ v' → √l-cat {w = []} {v = v'} ∘g π v'))
       (√l-dist-proj {w = []} v)
  ∙ cong (_∘g π v) (√l-cat-ε {v = v})

-- right counit:  map□ ε□ ∘g δ ≡ id
□-counit-r : map□ ε□ ∘g δ ≡ id {A = □ A}
□-counit-r = {!!}

-- coassociativity:  δ ∘g δ ≡ map□ δ ∘g δ
□-coassoc : δ ∘g δ ≡ map□ δ ∘g δ {A = A}
□-coassoc = {!!}
