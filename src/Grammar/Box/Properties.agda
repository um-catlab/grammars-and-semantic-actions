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

-- The retract direction `&ᴰ-intro (λ x → √l-map (π x)) ∘g √l-dist ≡ id` follows
-- from √l-dist-proj + &ᴰ β/η.  The *section* direction below is the other
-- triangle of the iso `√l-string w (&ᴰ B) ≅ &ᴰ (√l-string w ∘ B)` (√w, a right
-- adjoint, preserves the &ᴰ-product).  Same ⌈⌉-uniqueness realignment as
-- √l-dist-proj/⌈⌉-realign-id, but recombining the whole family at once: pointwise
-- `√l-dist ∘ (λ x → √l-map (π x))` rebuilds `G pw` onto `pw`'s split, the
-- identity by ⌈ w ⌉-uniqueness (per-component Eq-transport killed by
-- eqTransportFiller).
opaque
  unfolding ⌈⌉-⊗&ᴰ-distL⁻Eq _⇒_ ⇒-app ⇒-intro _⊗_ ⊗-intro _&_ &-intro π₁ π₂
            uniquely-supported-⌈⌉Eq same-parses the-split
  √l-dist-section-pt :
    ∀ {ℓX ℓ} {X : Type ℓX} {B : X → Grammar ℓ} {w}
      (u : String) (G : √l-string w (&[ x ∈ X ] B x) u)
    → (√l-dist {w = w} {B = B} ∘g &ᴰ-intro (λ x → √l-map {w = w} (π x))) u G ≡ G
  √l-dist-section-pt {X = X} {B = B} {w = w} u G = funExt λ pw →
    ⊗≡ {A = ⌈ w ⌉} {B = &[ x ∈ X ] B x} {w = u} _ _ (sp≡ pw) (pp pw)
    where
      12≡ : ∀ pw → G pw .fst .fst .snd Eq.≡ pw .fst .fst .snd
      12≡ pw = ++-cancelˡEq (pw .fst .fst .fst)
        ( Eq.ap (_++ G pw .fst .fst .snd)
            ( Eq.sym (uniquely-supported-⌈⌉Eq w (pw .fst .fst .fst) (pw .snd .fst))
              Eq.∙ uniquely-supported-⌈⌉Eq w (G pw .fst .fst .fst) (G pw .snd .fst))
          Eq.∙ Eq.sym (G pw .fst .snd)
          Eq.∙ pw .fst .snd )

      lp : ∀ pw → pw .fst .fst .fst ≡ G pw .fst .fst .fst
      lp pw = eqToPath
        ( Eq.sym (uniquely-supported-⌈⌉Eq w (pw .fst .fst .fst) (pw .snd .fst))
          Eq.∙ uniquely-supported-⌈⌉Eq w (G pw .fst .fst .fst) (G pw .snd .fst))

      rp : ∀ pw → pw .fst .fst .snd ≡ G pw .fst .fst .snd
      rp pw = sym (eqToPath (12≡ pw))

      sp≡ : ∀ pw → pw .fst .fst ≡ G pw .fst .fst
      sp≡ pw = λ i → lp pw i , rp pw i

      pp : ∀ pw → PathP (λ i → ⌈ w ⌉ (sp≡ pw i .fst) × (&[ x ∈ X ] B x) (sp≡ pw i .snd))
                        (pw .snd .fst , λ x → Eq.transport (B x) (12≡ pw) (G pw .snd .snd x))
                        (G pw .snd)
      pp pw = ΣPathP
        ( isProp→PathP (λ i → isLang⌈⌉ w (lp pw i)) _ _
        , λ i x → symP (eqTransportFiller (B x) (12≡ pw) (G pw .snd .snd x)) i )

  √l-dist-section :
    ∀ {ℓX ℓ} {X : Type ℓX} {B : X → Grammar ℓ} {w}
    → √l-dist {w = w} {B = B} ∘g &ᴰ-intro (λ x → √l-map {w = w} (π x)) ≡ id
  √l-dist-section {B = B} {w = w} =
    funExt λ u → funExt λ G → √l-dist-section-pt {B = B} {w = w} u G

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

-- naturality of Eq.transport: a fibrewise map commutes with transport.
Eq-transport-nat : ∀ {ℓ ℓp ℓq} {X : Type ℓ} {a b : X}
  (P : X → Type ℓp) (Q : X → Type ℓq)
  (h : ∀ z → P z → Q z) (e : a Eq.≡ b) (x : P a)
  → Eq.transport Q e (h a x) ≡ h b (Eq.transport P e x)
Eq-transport-nat P Q h Eq.refl x = refl

-- A self-`Eq`-equality between *strings* (which form a set) carries no
-- transport content: `Eq.transport P e ≡ id`.  This is the key to unsticking
-- √l-cat's internal transports along `r2 Eq.≡ r2`-style self-equalities.
Eq-transport-self : ∀ {ℓp} {a : String}
  (P : String → Type ℓp) (e : a Eq.≡ a) (x : P a)
  → Eq.transport P e x ≡ x
Eq-transport-self {a = a} P e x =
  cong (λ p → Eq.transport P p x) (isSetEqString a a e Eq.refl)

-- Eq.transport composes along `Eq._∙_` (definitional: `refl ∙ q = q`,
-- `Eq.transport P refl x = x`).
Eq-transport-∙ : ∀ {ℓ ℓp} {X : Type ℓ} {a b c : X}
  (P : X → Type ℓp) (p : a Eq.≡ b) (q : b Eq.≡ c) (x : P a)
  → Eq.transport P q (Eq.transport P p x) ≡ Eq.transport P (p Eq.∙ q) x
Eq-transport-∙ P Eq.refl q x = refl

-- Transporting a `⌈ z ⌉ ⊗ C`-shaped Σ in the ⌈⌉-index `z` only moves the
-- ⌈ z ⌉-factor; the C-component (and the splitting) are untouched.  Stated
-- over an explicit Σ (so no opaque `⊗`-projection appears in the type) and
-- matched on `refl`.  Used to strip the residual `++-assoc` index-cast that
-- `transport-fun` leaves on the RHS C-element of the pentagon.
strip-transport : ∀ {ℓs ℓg ℓc} {S : Type ℓs} {a b : String}
  (G : String → S → Type ℓg) (Cf : S → Type ℓc)
  (e : a Eq.≡ b) (s₀ : S) (g : G a s₀) (c : Cf s₀)
  → Eq.transport (λ z → Σ S (λ s → G z s × Cf s)) e (s₀ , g , c)
    ≡ (s₀ , Eq.transport (λ z → G z s₀) e g , c)
strip-transport G Cf Eq.refl s₀ g c = refl

-- (⌈ s ⌉ ⊗ ⊤) u is a proposition: the ⌈ s ⌉-prefix forces the split.
opaque
  unfolding _⊗_ ⊤ same-parses the-split
  ⌈⌉⊗⊤-isProp : ∀ {s} (u : String) (p q : (⌈ s ⌉ ⊗ ⊤) u) → p ≡ q
  ⌈⌉⊗⊤-isProp {s = s} u p q =
    ⊗≡ {A = ⌈ s ⌉} {B = ⊤} {w = u} p q
      (unique-splitting-⌈⌉L s u p q)
      (ΣPathP ( isProp→PathP (λ i → isLang⌈⌉ s _) _ _
              , isProp→PathP (λ i → isPropUnit) _ _ ))

  -- … and more generally ⌈ s ⌉ ⊗ P is a prop whenever P is.
  ⌈⌉⊗-isProp : ∀ {ℓ} {P : Grammar ℓ} (isP : ∀ u → isProp (P u))
    → ∀ {s} (u : String) (p q : (⌈ s ⌉ ⊗ P) u) → p ≡ q
  ⌈⌉⊗-isProp {P = P} isP {s = s} u p q =
    ⊗≡ {A = ⌈ s ⌉} {B = P} {w = u} p q
      (unique-splitting-⌈⌉L s u p q)
      (ΣPathP ( isProp→PathP (λ i → isLang⌈⌉ s _) _ _
              , isProp→PathP (λ i → isP _) _ _ ))

-- √l-string w and □ preserve "being a prop grammar" (√w = (⌈w⌉⊗⊤) ⇒ (⌈w⌉⊗-),
-- a function into a prop; □ is a &ᴰ of those).
opaque
  unfolding ⊤
  ⊤-isProp : ∀ u → isProp (⊤ u)
  ⊤-isProp u = isPropUnit

opaque
  unfolding _⇒_
  √l-string-isProp : ∀ {ℓ} {X : Grammar ℓ} → (∀ u → isProp (X u))
    → ∀ {w} u → isProp (√l-string w X u)
  √l-string-isProp {X = X} isX {w = w} u =
    isPropΠ (λ _ → ⌈⌉⊗-isProp {P = X} isX {s = w} u)

□-isProp : ∀ {ℓ} {X : Grammar ℓ} → (∀ u → isProp (X u))
  → ∀ u → isProp ((□ X) u)
□-isProp isX u = isPropΠ (λ w → √l-string-isProp isX {w = w} u)

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

      leftPath : pw .fst .fst .fst ≡ q' .fst .fst .fst
      leftPath =
          eqToPath (Eq.sym (uniquely-supported-⌈⌉Eq w (pw .fst .fst .fst)
                              (pw .snd .fst)))
        ∙ eqToPath (Eq.sym (++-unit-r-Eq w))
        ∙ eqToPath (uniquely-supported-⌈⌉Eq (w ++ []) (q' .fst .fst .fst)
                      (q' .snd .fst))

      -- √l-cat {w} {[]}'s reconstructed input at the trivial inner []-peel
      -- (matches √l-cat's source, so the unfolded LHS is defeq to the realign).
      input₀ : (⌈ w ++ [] ⌉ ⊗ ⊤) u
      input₀ =
        ( (( pw .fst .fst .fst ++ [] , pw .fst .fst .snd )
          , ( pw .fst .snd
              Eq.∙ Eq.ap (pw .fst .fst .fst ++_) Eq.refl
              Eq.∙ Eq.sym (++-assoc-Eq (pw .fst .fst .fst) [] (pw .fst .fst .snd)) ))
        , ( ⌈⌉-++ w [] (pw .fst .fst .fst ++ [])
              ((( pw .fst .fst .fst , [] ) , Eq.refl) , (pw .snd .fst , ε-intro))
          , _ ) )

      ra : d input₀ .fst .fst .snd Eq.≡ pw .fst .fst .snd
      ra =
        ++-cancelˡEq (pw .fst .fst .fst ++ [])
          ( Eq.ap (_++ d input₀ .fst .fst .snd)
              (Eq.sym
                ( Eq.sym (uniquely-supported-⌈⌉Eq (w ++ []) (d input₀ .fst .fst .fst)
                            (d input₀ .snd .fst))
                  Eq.∙ Eq.ap (_++ []) (uniquely-supported-⌈⌉Eq w (pw .fst .fst .fst)
                                         (pw .snd .fst))
                  Eq.∙ Eq.ap (pw .fst .fst .fst ++_)
                        (uniquely-supported-⌈⌉Eq [] [] ε-intro) ))
            Eq.∙ Eq.sym (d input₀ .fst .snd)
            Eq.∙ ( pw .fst .snd
                   Eq.∙ Eq.ap (pw .fst .fst .fst ++_) Eq.refl
                   Eq.∙ Eq.sym (++-assoc-Eq (pw .fst .fst .fst) []
                                 (pw .fst .fst .snd)) ) )

      dpath : d input₀ ≡ d pw*
      dpath = cong d
        (ΣPathP ( SplittingEqPathP {w = λ _ → u}
                    (unique-splitting-⌈⌉L (w ++ []) u input₀ pw*)
                , ΣPathP ( isProp→PathP (λ i → isLang⌈⌉ (w ++ []) _) _ _
                         , isProp→PathP (λ i → isPropUnit) _ _ ) ))

      sp≡ : pw .fst .fst ≡ q' .fst .fst
      sp≡ = λ i →
        ( leftPath i
        , ( sym (eqToPath ra) ∙ cong (λ z → z .fst .fst .snd) dpath ) i )

      pp = ΣPathP
        ( isProp→PathP (λ i → isLang⌈⌉ w (leftPath i)) _ _
        , compPathP' {B = A}
            (symP (eqTransportFiller A ra (d input₀ .snd .snd)))
            (λ i → dpath i .snd .snd) )
    in ⊗≡ {A = ⌈ w ⌉} {B = A} {w = u} _ rhs' sp≡ pp ∙ sym moves

-- naturality of √l-cat in the grammar argument.  Both composites send d to the
-- same repackaging: reconstruct the (w++v)-input from (pw,pv), apply d, and put
-- the deep A-output through f.  The two sides agree on every splitting/⌈⌉ part
-- on the nose (refl); they differ only by f-before-transport vs
-- transport-before-f at the innermost element, i.e. by Eq-transport-nat.
opaque
  unfolding √l-cat _⇒_ ⇒-app ⇒-intro _⊗_ ⊗-intro same-parses the-split
  √l-cat-nat : ∀ {ℓA ℓB} {A : Grammar ℓA} {B : Grammar ℓB} {w v : String}
    (f : A ⊢ B)
    → √l-cat {A = B} {w = w} {v = v} ∘g √l-map {w = w ++ v} f
      ≡ √l-map {w = w} (√l-map {w = v} f) ∘g √l-cat {A = A} {w = w} {v = v}
  √l-cat-nat {A = A} {B = B} {w = w} {v = v} f =
    funExt λ u → funExt λ d → funExt λ pw →
      ⊗≡ {A = ⌈ w ⌉} {B = √l-string v B} {w = u} _ _ refl
        (ΣPathP (refl ,
          funExt λ pv →
            ⊗≡ {A = ⌈ v ⌉} {B = B} {w = pw .fst .fst .snd} _ _ refl
              (ΣPathP (refl , Eq-transport-nat A B f _ _))))

-- `d`-image irrelevance (the device that moves the √l-cat pentagon's deepest
-- obligation into a *constant* C-fibre `C r`, where it becomes a plain path).
-- Stated abstractly over the input prop `P`, its "output position" `pos`, and
-- the "output C-element" `cel`, so no opaque `⊗`-projection appears in the
-- type.  At the call site one instantiates `P := (⌈ s ⌉ ⊗ ⊤) u₀` (a prop by
-- `⌈⌉⊗⊤-isProp`), `pos x := d x .fst .fst .snd`, `cel x := d x .snd .snd`.
-- Pure consequence of `isP` + the fact that `Eq`-equalities between strings
-- are a prop (`isSetEqString`).
d-image-irrel : ∀ {ℓ ℓC'} {C' : Grammar ℓC'} {r : String}
  {P : Type ℓ} (isP : isProp P)
  (pos : P → String) (cel : (x : P) → C' (pos x))
  (i j : P) (pi : pos i Eq.≡ r) (pj : pos j Eq.≡ r)
  → Eq.transport C' pi (cel i) ≡ Eq.transport C' pj (cel j)
d-image-irrel {C' = C'} {r = r} isP pos cel i j pi pj k =
  Eq.transport C' (β k) (cel (isP i j k))
  where
    β : PathP (λ k → pos (isP i j k) Eq.≡ r) pi pj
    β = isProp→PathP (λ k → isSetEqString (pos (isP i j k)) r) pi pj

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

-- √l-cat PENTAGON (associativity of the suffix peel).  The two ways of peeling
-- `(w ++ v) ++ u` — peel `w++v` then `u`, vs peel `w` then `v++u` — agree, modulo
-- the index cast `√l-castEq ((w++v)++u ≡ w++(v++u))`.  This is the core geometric
-- fact behind □-coassoc.  Pointwise it is the same realign/eqTransportFiller
-- argument as √l-cat-εr, now with the reconstructed input triply nested
-- (w' , v' , u') and the splitting path coming from ++-assoc-Eq.
opaque
  unfolding √l-cat _⇒_ ⇒-app ⇒-intro _⊗_ ⊗-intro same-parses the-split
            uniquely-supported-⌈⌉Eq
  √l-cat-assoc : ∀ {ℓC} {C : Grammar ℓC} {w v u : String}
    → √l-cat {A = √l-string u C} {w = w} {v = v}
        ∘g √l-cat {A = C} {w = w ++ v} {v = u}
      ≡ √l-map {w = w} (√l-cat {A = C} {w = v} {v = u})
        ∘g √l-cat {A = C} {w = w} {v = v ++ u}
        ∘g √l-castEq {C = C} (++-assoc-Eq w v u)
  √l-cat-assoc {C = C} {w = w} {v = v} {u = u} =
    funExt λ u₀ → funExt λ d → funExt λ pw →
      ⊗≡ {A = ⌈ w ⌉} {B = √l-string v (√l-string u C)} {w = u₀} _ _ refl
        -- w- and v-level splits are refl (√l-cat preserves the outer split).
        (ΣPathP (refl , funExt λ pv →
          ⊗≡ {A = ⌈ v ⌉} {B = √l-string u C} {w = pw .fst .fst .snd} _ _ refl
            (ΣPathP (refl , funExt λ pu →
              -- u-level.  All three splittings are now done: the w/v splits are
              -- refl, and the u-split is forced by ⌈u⌉-uniqueness
              -- (unique-splitting-⌈⌉L).  The remaining `same-parses` hole is the
              -- ⌈u⌉-proof PathP (free, isLang⌈⌉) together with the deep C-element
              -- PathP — the genuine content:
              --   LHS C-elem = (Eq.transport (√l-string u C) ra_wv (Da.snd.snd)) pu .snd
              --   RHS C-elem = Eq.transport C ra_vu (db.snd.snd)
              -- i.e. d applied to u₀'s unique decomposition w'++v'++u'++rest two
              -- ways (((w++v)++u) vs the ++-assoc-cast w++(v++u)); equal by
              -- transport coherence (toPathP / eqTransportFiller + dpath as in
              -- √l-cat-εr's `pp`).
              let lhsE = (√l-cat {A = √l-string u C} {w = w} {v = v}
                            ∘g √l-cat {A = C} {w = w ++ v} {v = u})
                           u₀ d pw .snd .snd pv .snd .snd pu
                  rhsE = (√l-map {w = w} (√l-cat {A = C} {w = v} {v = u})
                            ∘g √l-cat {A = C} {w = w} {v = v ++ u}
                            ∘g √l-castEq {C = C} (++-assoc-Eq w v u))
                           u₀ d pw .snd .snd pv .snd .snd pu
              in ⊗≡ {A = ⌈ u ⌉} {B = C} {w = pv .fst .fst .snd} lhsE rhsE
                (unique-splitting-⌈⌉L u (pv .fst .fst .snd) lhsE rhsE)
                -- The deep C-element PathP.  Plan:
                --  • unstick the LHS: the outer √l-cat transport is along a
                --    self-equality `r2 Eq.≡ r2`, hence ≡ refl (Eq-transport-self);
                --  • unstick the RHS: push the ++-assoc cast inside `d`
                --    (transport-fun) and strip the residual index-cast off the
                --    C-element (strip-transport);
                --  • bridge `d inL` and `d inR'` in the *constant* fibre `C r3`
                --    via d-image-irrel (their inputs agree by ⌈⌉⊗⊤-isProp);
                --  • realign the PathP base to `s≡ .snd` via isSetString.
                (ΣPathP (isProp→PathP (λ i → isLang⌈⌉ u _) _ _ ,
                  -- Assembly (structure machine-checked: with the fill below the
                  -- file has *no type errors*, only the RHS-strip residual unsolved):
                  --   subst (λ β → PathP (λ i → C (β i)) (lhsE .snd .snd) (rhsE .snd .snd))
                  --     (isSetString _ _ _ _)
                  --     (compPathP' {B = C}
                  --        -- LHS unstick: outer √l-cat transport is a self-eq r2≡r2
                  --        (λ i → cong (λ f → f pu)
                  --                 (Eq-transport-self (√l-string u C) _ _) i .snd .snd)
                  --        (compPathP' {B = C}
                  --           -- bridge in the constant fibre C r3
                  --           ( d-image-irrel {C' = C} (⌈⌉⊗⊤-isProp u₀)
                  --               (λ x → d x .fst .fst .snd) (λ x → d x .snd .snd) _ _ _ _
                  --           ∙ sym (Eq-transport-∙ C _ _ _)
                  --           ∙ cong (λ x → Eq.transport C _ (Eq.transport C _ x))
                  --                  (sym (cong (λ p → p .snd .snd)
                  --                         (strip-transport (λ z s → ⌈ z ⌉ (s .fst .fst))
                  --                           (λ s → C (s .fst .snd)) (++-assoc-Eq w v u)
                  --                           sR gR cR))) )  -- ⇐ sR,gR,cR = `d inR'` decomposed
                  --           -- RHS unstick: push the ++-assoc cast inside d
                  --           (symP (λ i →
                  --              cong (λ cv → (√l-map {w = w} (√l-cat {A = C} {w = v} {v = u})
                  --                      ∘g √l-cat {A = C} {w = w} {v = v ++ u})
                  --                      u₀ cv pw .snd .snd pv .snd .snd pu)
                  --                 (funExt (λ inp →
                  --                    transport-fun (λ z → (⌈ z ⌉ ⊗ ⊤) u₀)
                  --                      (λ z → (⌈ z ⌉ ⊗ C) u₀) (++-assoc-Eq w v u) d inp))
                  --                 i .snd .snd))))
                  -- Only `sR gR cR` (the cast-back d-input `d inR'`, decomposed) is
                  -- missing: reducing it exposes √l-cat's `where`-internals, which are
                  -- unnameable in source.  Fill interactively (C-c C-a / refine on the
                  -- Eq.refls), where the goal-directed solver supplies them.
                  {!!}))))))

-- Generic mono-from-retract: if `r ∘g s ≡ id`, then `s` is monic.
mono-by-retract : ∀ {ℓx ℓy ℓz} {X : Grammar ℓx} {Y : Grammar ℓy} {Z : Grammar ℓz}
  (r : Y ⊢ X) (s : X ⊢ Y) → r ∘g s ≡ id
  → (g₁ g₂ : Z ⊢ X) → s ∘g g₁ ≡ s ∘g g₂ → g₁ ≡ g₂
mono-by-retract r s ret g₁ g₂ hyp =
    sym (cong (_∘g g₁) ret) ∙ cong (r ∘g_) hyp ∙ cong (_∘g g₂) ret

-- The section of √l-dist (its inverse): `λ x → √l-map (π x)`, packaged.
√l-undist : ∀ {ℓ ℓX} {X : Type ℓX} {B : X → Grammar ℓ} {w}
  → √l-string w (&[ x ∈ X ] B x) ⊢ &[ x ∈ X ] √l-string w (B x)
√l-undist {B = B} {w = w} = &ᴰ-intro (λ x → √l-map {w = w} (π x))

-- √l-dist is split epi (section √l-undist); hence √l-undist is monic.
√l-undist-mono : ∀ {ℓ ℓX ℓz} {X : Type ℓX} {B : X → Grammar ℓ} {w} {Z : Grammar ℓz}
  (g₁ g₂ : Z ⊢ √l-string w (&[ x ∈ X ] B x))
  → √l-undist {B = B} {w = w} ∘g g₁ ≡ √l-undist {B = B} {w = w} ∘g g₂ → g₁ ≡ g₂
√l-undist-mono {B = B} {w = w} =
  mono-by-retract (√l-dist {w = w} {B = B}) (√l-undist {B = B} {w = w})
    (√l-dist-section {B = B} {w = w})

-- coassociativity:  δ ∘g δ ≡ map□ δ ∘g δ
--
-- Per outer index w (then v, then u), each level stripped by a √l-dist/√l-map
-- mono.  Projecting the innermost □A's u-component, BOTH sides collapse — via
-- √l-cat-nat + √l-dist-proj + √l-map-seq + &ᴰ β — to the two legs of the √l-cat
-- pentagon precomposed with π:
--   LHS → √l-cat {w}{v} ∘ √l-cat {w++v}{u} ∘ π ((w++v)++u)
--   RHS → √l-map {w}(√l-cat {v}{u}) ∘ √l-cat {w}{v++u} ∘ π (w++(v++u))
-- which agree by √l-cat-assoc + castπ.  (No √l-cat/√l-dist interchange needed:
-- projecting first lets √l-dist-proj eat every √l-dist before comparison.)
□-coassoc : δ ∘g δ ≡ map□ δ ∘g δ {A = A}
□-coassoc {A = A} = &ᴰ≡ _ _ λ w →
  √l-undist-mono {B = λ z → √l-string z (□ A)} {w = w} _ _
    (&ᴰ≡ _ _ λ v → step-v w v)
  where
    -- δ's inner family at index w (residual grammar A), and at residual □A.
    innerδ : (w : String) → □ A ⊢ &[ v ∈ String ] √l-string w (√l-string v A)
    innerδ w = &ᴰ-intro (λ v → √l-cat {A = A} {w = w} {v = v}
                              ∘g π {A = λ z → √l-string z A} (w ++ v))
    innerδ□ : (w : String) → □ (□ A) ⊢ &[ v ∈ String ] √l-string w (√l-string v (□ A))
    innerδ□ w = &ᴰ-intro (λ v → √l-cat {A = □ A} {w = w} {v = v}
                               ∘g π {A = λ z → √l-string z (□ A)} (w ++ v))

    LHS-wv : (w v : String) → □ A ⊢ √l-string w (√l-string v (□ A))
    LHS-wv w v =
      √l-cat {A = □ A} {w = w} {v = v}
        ∘g √l-dist {w = w ++ v} {B = λ z → √l-string z A}
        ∘g innerδ (w ++ v)

    RHS-wv : (w v : String) → □ A ⊢ √l-string w (√l-string v (□ A))
    RHS-wv w v =
      √l-map {w = w} (√l-dist {w = v} {B = λ z → √l-string z A} ∘g innerδ v)
        ∘g √l-dist {w = w} {B = λ z → √l-string z A}
        ∘g innerδ w

    -- The √l-string-tower mono for the inner □A, and its retraction.
    Φ̃ : (w v : String) → √l-string w (√l-string v (□ A))
        ⊢ &[ u ∈ String ] √l-string w (√l-string v (√l-string u A))
    Φ̃ w v = √l-undist {B = λ u → √l-string v (√l-string u A)} {w = w}
              ∘g √l-map {w = w} (√l-undist {B = λ z → √l-string z A} {w = v})
    Ψ̃ : (w v : String) → (&[ u ∈ String ] √l-string w (√l-string v (√l-string u A)))
        ⊢ √l-string w (√l-string v (□ A))
    Ψ̃ w v = √l-map {w = w} (√l-dist {w = v} {B = λ z → √l-string z A})
              ∘g √l-dist {w = w} {B = λ u → √l-string v (√l-string u A)}
    retΦ̃ : (w v : String) → Ψ̃ w v ∘g Φ̃ w v ≡ id
    retΦ̃ w v =
        cong (√l-map {w = w} (√l-dist {w = v} {B = λ z → √l-string z A}) ∘g_)
          (cong (_∘g √l-map {w = w} (√l-undist {B = λ z → √l-string z A} {w = v}))
                (√l-dist-section {B = λ u → √l-string v (√l-string u A)} {w = w}))
      ∙ sym (√l-map-seq {w = w} (√l-undist {B = λ z → √l-string z A} {w = v})
                                (√l-dist {w = v} {B = λ z → √l-string z A}))
      ∙ cong (√l-map {w = w}) (√l-dist-section {B = λ z → √l-string z A} {w = v})
      ∙ √l-map-id {w = w}

    -- π u ∘g Φ̃ reassociates to √l-map{w}(√l-map{v}(π u)).
    Φ̃-proj : (w v u : String)
      → √l-map {w = w} (π {A = λ x → √l-string v (√l-string x A)} u)
          ∘g √l-map {w = w} (√l-undist {B = λ z → √l-string z A} {w = v})
        ≡ √l-map {w = w} (√l-map {w = v} (π {A = λ z → √l-string z A} u))
    Φ̃-proj w v u =
      sym (√l-map-seq {w = w} (√l-undist {B = λ z → √l-string z A} {w = v})
                              (π {A = λ x → √l-string v (√l-string x A)} u))

    -- RHS leg: reduce √l-map{w}(√l-map{v}(π u)) ∘ RHS-wv to the pentagon's
    -- second leg precomposed with π.
    RHS-leg : (w v u : String)
      → √l-map {w = w} (√l-map {w = v} (π {A = λ z → √l-string z A} u)) ∘g RHS-wv w v
        ≡ √l-map {w = w} (√l-cat {A = A} {w = v} {v = u})
          ∘g √l-cat {A = A} {w = w} {v = v ++ u}
          ∘g π {A = λ z → √l-string z A} (w ++ (v ++ u))
    RHS-leg w v u =
        cong (_∘g (√l-dist {w = w} {B = λ z → √l-string z A} ∘g innerδ w))
          (sym (√l-map-seq {w = w}
                  (√l-dist {w = v} {B = λ z → √l-string z A} ∘g innerδ v)
                  (√l-map {w = v} (π {A = λ z → √l-string z A} u))))
      ∙ cong (λ z → √l-map {w = w} (z ∘g innerδ v)
                    ∘g √l-dist {w = w} {B = λ z → √l-string z A} ∘g innerδ w)
          (√l-dist-proj {B = λ z → √l-string z A} {w = v} u)
      ∙ cong (λ z → z ∘g √l-dist {w = w} {B = λ z → √l-string z A} ∘g innerδ w)
          (√l-map-seq {w = w} (π {A = λ z → √l-string z A} (v ++ u))
                              (√l-cat {A = A} {w = v} {v = u}))
      ∙ cong (λ z → √l-map {w = w} (√l-cat {A = A} {w = v} {v = u})
                    ∘g z ∘g innerδ w)
          (√l-dist-proj {B = λ z → √l-string z A} {w = w} (v ++ u))

    -- the pentagon-leg equality after projecting the u-component.
    pentagon-leg : (w v u : String)
      → √l-map {w = w} (√l-map {w = v} (π {A = λ z → √l-string z A} u)) ∘g LHS-wv w v
        ≡ √l-map {w = w} (√l-map {w = v} (π {A = λ z → √l-string z A} u)) ∘g RHS-wv w v
    pentagon-leg w v u =
        cong (_∘g (√l-dist {w = w ++ v} {B = λ z → √l-string z A} ∘g innerδ (w ++ v)))
          (sym (√l-cat-nat {w = w} {v = v} (π {A = λ z → √l-string z A} u)))
      ∙ cong (λ z → √l-cat {A = √l-string u A} {w = w} {v = v} ∘g z ∘g innerδ (w ++ v))
          (√l-dist-proj {B = λ z → √l-string z A} {w = w ++ v} u)
      ∙ cong (_∘g π {A = λ z → √l-string z A} ((w ++ v) ++ u))
          (√l-cat-assoc {C = A} {w = w} {v = v} {u = u})
      ∙ cong (λ z → √l-map {w = w} (√l-cat {A = A} {w = v} {v = u})
                    ∘g √l-cat {A = A} {w = w} {v = v ++ u} ∘g z)
          (castπ {A = A} (++-assoc-Eq w v u))
      ∙ sym (RHS-leg w v u)

    inner-eq : (w v : String) → LHS-wv w v ≡ RHS-wv w v
    inner-eq w v =
      mono-by-retract (Ψ̃ w v) (Φ̃ w v) (retΦ̃ w v) (LHS-wv w v) (RHS-wv w v)
        (&ᴰ≡ _ _ λ u →
            cong (_∘g LHS-wv w v) (Φ̃-proj w v u)
          ∙ pentagon-leg w v u
          ∙ sym (cong (_∘g RHS-wv w v) (Φ̃-proj w v u)))

    step-v : (w v : String)
      → √l-map {w = w} (π {A = λ z → √l-string z (□ A)} v)
          ∘g (π {A = λ z → √l-string z (□ (□ A))} w ∘g (δ ∘g δ))
        ≡ √l-map {w = w} (π {A = λ z → √l-string z (□ A)} v)
          ∘g (π {A = λ z → √l-string z (□ (□ A))} w ∘g (map□ δ ∘g δ))
    step-v w v =
        cong (_∘g (innerδ□ w ∘g δ))
          (√l-dist-proj {B = λ z → √l-string z (□ A)} {w = w} v)
      ∙ inner-eq w v
      ∙ cong (_∘g (√l-dist {w = w} {B = λ z → √l-string z A} ∘g innerδ w))
          (√l-map-seq {w = w} δ (π {A = λ z → √l-string z (□ A)} v))
