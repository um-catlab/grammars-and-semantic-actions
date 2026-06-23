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
open import Grammar.External.String.Tiny Alphabet
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

-- The x-component of `⌈⌉-⊗&ᴰ-distL⁻Eq` (opaque wrapper so the type signature
-- mentions no `_⊗_`-projections): rebuild `q : ⌈ w ⌉ ⊗ C` onto `s⊤`'s split.
opaque
  unfolding _⊗_ uniquely-supported-⌈⌉Eq
  realign-split :
    ∀ {ℓC} {C : Grammar ℓC} {w} (u : String)
    → (⌈ w ⌉ ⊗ C) u → (⌈ w ⌉ ⊗ ⊤) u → (⌈ w ⌉ ⊗ C) u
  realign-split {C = C} {w = w} u q s⊤ =
    s⊤ .fst , (s⊤ .snd .fst , Eq.transport C 12≡ (q .snd .snd))
    where
      12≡ : q .fst .fst .snd Eq.≡ s⊤ .fst .fst .snd
      12≡ = ++-cancelˡEq (s⊤ .fst .fst .fst)
        ( Eq.ap (_++ q .fst .fst .snd)
            ( Eq.sym (uniquely-supported-⌈⌉Eq w (s⊤ .fst .fst .fst) (s⊤ .snd .fst))
              Eq.∙ uniquely-supported-⌈⌉Eq w (q .fst .fst .fst) (q .snd .fst))
          Eq.∙ Eq.sym (q .fst .snd)
          Eq.∙ s⊤ .fst .snd )

-- That realignment is the identity (forced by ⌈ w ⌉-uniqueness).  Stated over a
-- generic `q` so no neutral box-projection appears (avoids higher-order metas).
opaque
  unfolding realign-split _⊗_ uniquely-supported-⌈⌉Eq same-parses the-split
  ⌈⌉-realign-id :
    ∀ {ℓC} {C : Grammar ℓC} {w} (u : String)
      (q : (⌈ w ⌉ ⊗ C) u) (s⊤ : (⌈ w ⌉ ⊗ ⊤) u)
    → realign-split {C = C} {w = w} u q s⊤ ≡ q
  ⌈⌉-realign-id {C = C} {w = w} u q s⊤ =
    ⊗≡ {A = ⌈ w ⌉} {B = C} {w = u} _ _ sp≡ pp
    where
      12≡ : q .fst .fst .snd Eq.≡ s⊤ .fst .fst .snd
      12≡ = ++-cancelˡEq (s⊤ .fst .fst .fst)
        ( Eq.ap (_++ q .fst .fst .snd)
            ( Eq.sym (uniquely-supported-⌈⌉Eq w (s⊤ .fst .fst .fst) (s⊤ .snd .fst))
              Eq.∙ uniquely-supported-⌈⌉Eq w (q .fst .fst .fst) (q .snd .fst))
          Eq.∙ Eq.sym (q .fst .snd)
          Eq.∙ s⊤ .fst .snd )

      lp : s⊤ .fst .fst .fst ≡ q .fst .fst .fst
      lp = eqToPath
        ( Eq.sym (uniquely-supported-⌈⌉Eq w (s⊤ .fst .fst .fst) (s⊤ .snd .fst))
          Eq.∙ uniquely-supported-⌈⌉Eq w (q .fst .fst .fst) (q .snd .fst))

      rp : s⊤ .fst .fst .snd ≡ q .fst .fst .snd
      rp = sym (eqToPath 12≡)

      sp≡ : s⊤ .fst .fst ≡ q .fst .fst
      sp≡ = λ i → lp i , rp i

      pp : PathP (λ i → ⌈ w ⌉ (sp≡ i .fst) × C (sp≡ i .snd))
                 (s⊤ .snd .fst , Eq.transport C 12≡ (q .snd .snd))
                 (q .snd)
      pp = ΣPathP
        ( isProp→PathP (λ i → isLang⌈⌉ w (lp i)) _ _
        , symP (eqTransportFiller C 12≡ (q .snd .snd)) )

-- `realign-split` packaged as a √l-string-endomap (clean signature), and the
-- fact that it is the identity (proved for an abstract `d`, so no neutral
-- box-projection ever appears).
opaque
  unfolding realign-split _⇒_
  realign-√l :
    ∀ {ℓC} {C : Grammar ℓC} {w} (u : String)
    → √l-string w C u → √l-string w C u
  realign-√l {C = C} {w = w} u d = λ pw → realign-split {C = C} {w = w} u (d pw) pw

  realign-√l-id :
    ∀ {ℓC} {C : Grammar ℓC} {w} (u : String) (d : √l-string w C u)
    → realign-√l {C = C} {w = w} u d ≡ d
  realign-√l-id {C = C} {w = w} u d =
    funExt λ pw → ⌈⌉-realign-id {C = C} {w = w} u (d pw) pw

-- projecting a component after √l-dist is the same as projecting it first.
-- Step 1 (pure conversion): the left side IS `realign-√l` of the x-component.
opaque
  unfolding realign-√l realign-split ⌈⌉-⊗&ᴰ-distL⁻Eq _⇒_ ⇒-app ⇒-intro _⊗_
            ⊗-intro _&_ &-intro π₁ π₂ uniquely-supported-⌈⌉Eq
  √l-dist-proj-reduce :
    ∀ {ℓX} {X : Type ℓX} {B : X → Grammar ℓA} {w} (x : X)
      (u : String) (F : (&[ y ∈ X ] √l-string w (B y)) u)
    → (√l-map {w = w} (π x) ∘g √l-dist {w = w} {B = B}) u F
      ≡ realign-√l {C = B x} {w = w} u (F x)
  √l-dist-proj-reduce x u F = funExt λ pw → refl

-- Step 2: combine.
√l-dist-proj-pt :
  ∀ {ℓX} {X : Type ℓX} {B : X → Grammar ℓA} {w} (x : X)
    (u : String) (F : (&[ y ∈ X ] √l-string w (B y)) u)
  → (√l-map {w = w} (π x) ∘g √l-dist {w = w} {B = B}) u F ≡ F x
√l-dist-proj-pt {B = B} {w = w} x u F =
  √l-dist-proj-reduce x u F ∙ realign-√l-id {C = B x} {w = w} u (F x)

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

-- index cast for √l-string (along an Eq-path of prefixes) and its π-coherence.
√l-castEq : ∀ {ℓC} {C : Grammar ℓC} {w w'} → w' Eq.≡ w → √l-string w' C ⊢ √l-string w C
√l-castEq {C = C} e u d = Eq.transport (λ z → √l-string z C u) e d

castπ : ∀ {w w'} (e : w' Eq.≡ w)
  → √l-castEq {C = A} e ∘g π {A = λ z → √l-string z A} w' ≡ π w
castπ Eq.refl = refl

-- Abstract Eq.transport lemmas (statements mention no opaque grammar
-- combinators, so they sidestep the opaque-in-signature wall).
transport-fun : ∀ {ℓ ℓp ℓq} {X : Type ℓ} {a b : X}
  (P : X → Type ℓp) (Q : X → Type ℓq)
  (e : a Eq.≡ b) (f : P a → Q a) (x : P b)
  → (Eq.transport (λ z → P z → Q z) e f) x
    ≡ Eq.transport Q e (f (Eq.transport P (Eq.sym e) x))
transport-fun P Q Eq.refl f x = refl

transport-Σ-fst : ∀ {ℓ ℓs ℓf} {X : Type ℓ} {a b : X}
  (S : Type ℓs) (F : X → S → Type ℓf)
  (e : a Eq.≡ b) (q : Σ S (F a))
  → Eq.transport (λ z → Σ S (F z)) e q
    ≡ (q .fst , Eq.transport (λ z → F z (q .fst)) e (q .snd))
transport-Σ-fst S F Eq.refl q = refl

transport-×-fst : ∀ {ℓ ℓb ℓd} {X : Type ℓ} {a b : X}
  (B : X → Type ℓb) (D : Type ℓd)
  (e : a Eq.≡ b) (p : B a × D)
  → Eq.transport (λ z → B z × D) e p
    ≡ (Eq.transport B e (p .fst) , p .snd)
transport-×-fst B D Eq.refl p = refl

-- (⌈ s ⌉ ⊗ ⊤) u is a proposition: the ⌈ s ⌉-prefix forces the split.
opaque
  unfolding _⊗_ ⊤ same-parses the-split
  ⌈⌉⊗⊤-isProp : ∀ {s} (u : String) (p q : (⌈ s ⌉ ⊗ ⊤) u) → p ≡ q
  ⌈⌉⊗⊤-isProp {s = s} u p q =
    ⊗≡ {A = ⌈ s ⌉} {B = ⊤} {w = u} p q
      (unique-splitting-⌈⌉L s u p q)
      (ΣPathP ( isProp→PathP (λ i → isLang⌈⌉ s _) _ _
              , isProp→PathP (λ i → isPropUnit) _ _ ))

-- √l-cat right unit: peeling `w` then `[]` and dropping the []-peel is the
-- `w`-peel, up to the index cast `w ++ [] ≡ w`.
--
-- OBSTRUCTION (the only step that resisted): `√l-cat {w} {[]}` bakes the
-- *computed* prefix `w ++ []` into its DOMAIN while its CODOMAIN uses `w`, so
-- Eq.J on `++-unit-r-Eq w` cannot abstract the occurrence (J needs a variable,
-- not `w ++ []`), and a domain-generalized `√l-cat` ends up stuck on a
-- non-`refl` proof.  The pointwise route reduces (using `⌈⌉⊗⊤-isProp` to equate
-- the two `⌈w++[]⌉⊗⊤` inputs to the peel) to a transport-of-application lemma
-- `(transport_e d) pw ≡ transport_e (d (transport_{sym e} pw))`, which can only
-- be stated through an opaque application alias (opaque `⇒` doesn't unfold in
-- signatures) and that alias then trips a cubical `transp`-irrelevance check.
opaque
  unfolding √l-cat _⇒_ _⊗_ ⊤ ⊗-unit-l ⊗-unit-l⁻ ⊗-intro ⇒-app ⇒-intro &-intro
            π₁ uniquely-supported-⌈⌉Eq ε ε-intro same-parses the-split
  √l-cat-εr : ∀ {w} → √l-map {w = w} √l-ε ∘g √l-cat {A = A} {w = w} {v = []}
                       ≡ √l-castEq {C = A} (++-unit-r-Eq w)
  √l-cat-εr {A = A} {w = w} = funExt λ u → funExt λ d → funExt λ pw →
    let
      e : w ++ [] Eq.≡ w
      e = ++-unit-r-Eq w
      pw* : (⌈ w ++ [] ⌉ ⊗ ⊤) u
      pw* = Eq.transport (λ z → (⌈ z ⌉ ⊗ ⊤) u) (Eq.sym e) pw
      q' : (⌈ w ++ [] ⌉ ⊗ A) u
      q' = d pw*
      rhs' : (⌈ w ⌉ ⊗ A) u
      rhs' = q' .fst
           , ( Eq.transport (λ z → ⌈ z ⌉ (q' .fst .fst .fst)) e (q' .snd .fst)
             , q' .snd .snd )
      moves : √l-castEq {C = A} e u d pw ≡ rhs'
      moves =
        transport-fun (λ z → (⌈ z ⌉ ⊗ ⊤) u) (λ z → (⌈ z ⌉ ⊗ A) u) e d pw
        ∙ transport-Σ-fst _ (λ z s → ⌈ z ⌉ (s .fst .fst) × A (s .fst .snd)) e q'
        ∙ cong (λ p → q' .fst , p)
            (transport-×-fst (λ z → ⌈ z ⌉ (q' .fst .fst .fst))
                             (A (q' .fst .fst .snd)) e (q' .snd))

      leftEq : pw .fst .fst .fst Eq.≡ q' .fst .fst .fst
      leftEq =
        Eq.sym (uniquely-supported-⌈⌉Eq w (pw .fst .fst .fst) (pw .snd .fst))
        Eq.∙ Eq.sym (++-unit-r-Eq w)
        Eq.∙ uniquely-supported-⌈⌉Eq (w ++ []) (q' .fst .fst .fst) (q' .snd .fst)

      rightEq : pw .fst .fst .snd Eq.≡ q' .fst .fst .snd
      rightEq =
        ++-cancelˡEq (pw .fst .fst .fst)
          ( Eq.sym (pw .fst .snd)
            Eq.∙ q' .fst .snd
            Eq.∙ Eq.ap (_++ q' .fst .fst .snd) (Eq.sym leftEq) )

      sp≡ : pw .fst .fst ≡ q' .fst .fst
      sp≡ = λ i → eqToPath leftEq i , eqToPath rightEq i

      pp : PathP (λ i → ⌈ w ⌉ (sp≡ i .fst) × A (sp≡ i .snd))
             (pw .snd .fst , {!!}) (rhs' .snd)
      pp = ΣPathP
        ( isProp→PathP (λ i → isLang⌈⌉ w (eqToPath leftEq i)) _ _
        , {!!} )
    in ⊗≡ {A = ⌈ w ⌉} {B = A} {w = u} _ rhs' sp≡ pp ∙ sym moves

-- right counit:  map□ ε□ ∘g δ ≡ id
-- π w ∘ map□ ε□ ∘ δ
--   = √l-map ε□ ∘ √l-dist[w] ∘ (λ v. √l-cat[w]v ∘ π (w++v))      [δ at w]
--   = √l-map √l-ε ∘ √l-map (π[]) ∘ √l-dist[w] ∘ (...)            [√l-map-seq]
--   = √l-map √l-ε ∘ π[] ∘ (...)                                  [√l-dist-proj]
--   = √l-map √l-ε ∘ √l-cat[w][] ∘ π (w++[])                      [&ᴰ β]
--   = √l-castEq (w++[]≡w) ∘ π (w++[])                            [√l-cat-εr]
--   = π w                                                        [castπ]
□-counit-r : map□ ε□ ∘g δ ≡ id {A = □ A}
□-counit-r {A = A} = &ᴰ≡ _ _ λ w →
  let innerδ : □ A ⊢ &[ v ∈ String ] √l-string w (√l-string v A)
      innerδ = &ᴰ-intro (λ v → √l-cat {A = A} {w = w} {v = v}
                              ∘g π {A = λ z → √l-string z A} (w ++ v))
  in
  cong (λ z → z ∘g √l-dist {w = w} {B = λ z → √l-string z A} ∘g innerδ)
       (√l-map-seq {w = w} (π {A = λ z → √l-string z A} []) √l-ε)
  ∙ cong (λ z → √l-map {w = w} √l-ε ∘g z ∘g innerδ)
       (√l-dist-proj {B = λ z → √l-string z A} {w = w} [])
  ∙ cong (√l-map {w = w} √l-ε ∘g_)
       (refl {x = √l-cat {A = A} {w = w} {v = []}
                  ∘g π {A = λ z → √l-string z A} (w ++ [])})
  ∙ cong (_∘g π {A = λ z → √l-string z A} (w ++ [])) (√l-cat-εr {A = A} {w = w})
  ∙ castπ (++-unit-r-Eq w)

-- coassociativity:  δ ∘g δ ≡ map□ δ ∘g δ
-- Reduces to the √l-cat *pentagon*: the two ways of factoring a
-- `(w ++ v ++ u)`-peel — `w` then `(v ++ u)` vs `(w ++ v)` then `u` — agree,
-- modulo the associativity path `(w ++ v) ++ u ≡ w ++ (v ++ u)`.  Builds on the
-- same realign/eqTransportFiller machinery; remaining.
□-coassoc : δ ∘g δ ≡ map□ δ ∘g δ {A = A}
□-coassoc = {!!}
