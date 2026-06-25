open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Box.Disjunction (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Data.Unit using (isPropUnit)
import Cubical.Data.Sum as Sum
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Equality using (eqToPath)

open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet using (ε)
open import Grammar.Top Alphabet
open import Grammar.Top.Properties Alphabet using (isLang⊤)
open import Grammar.Bottom Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.Distributivity Alphabet
open import Grammar.String Alphabet
open import Grammar.External.String.Tiny Alphabet
open import Grammar.Derivative.Disjunction Alphabet
open import Grammar.Properties Alphabet
  using (unambiguous; disjoint; isUnambiguousRetract')
open import Grammar.HLevels.Base Alphabet using (isLang)
open import Grammar.External.HLevels.Properties Alphabet
  using (isLang→unambiguous; unambiguous→isLang)
open import Grammar.Sum.Binary.AsPrimitive.Unambiguous Alphabet using (unambiguous⊕)
open import Grammar.Function.AsPrimitive.Properties Alphabet using (unambiguous⇒)
open import Grammar.Sum.Unambiguous Alphabet using (unambiguous⊕ᴰ)
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓX : Level
    A : Grammar ℓA
    B : Grammar ℓB

------------------------------------------------------------------------------
-- The □ comonad built on the DISJUNCTIVE √l (Grammar.Derivative.Disjunction):
--     □ A = &[ w ∈ String ] √l-string w A,   √l-string w A = (⌈w⌉⊗A) ⊕ ¬Start w.
-- Counit and functor action need no decidability; only the comultiplication
-- (its distributor `√l-dist`) does, since it must inspect `Start w`.
------------------------------------------------------------------------------

□_ : Grammar ℓA → Grammar ℓA
□ A = &[ w ∈ String ] √l-string w A

-- counit:  read off the []-component (√l-string [] A ≅ A)
ε□ : □ A ⊢ A
ε□ = √l-ε ∘g π []

-- functor action
map□ : A ⊢ B → □ A ⊢ □ B
map□ f = &ᴰ-intro λ w → √l-map {w = w} f ∘g π w

private
  variable
    ℓC : Level
    C : Grammar ℓC

------------------------------------------------------------------------------
-- Functoriality of √l-map / map□  (sum manipulation, no transports)
------------------------------------------------------------------------------

√l-map-id : ∀ {w} → √l-map {w = w} (id {A = A}) ≡ id
√l-map-id {A = A} {w = w} =
  cong (λ z → ⊕-elim (inl ∘g z) inr) (id,⊗id≡id {A = ⌈ w ⌉} {B = A})
  ∙ ⊕-η id

√l-map-seq : ∀ {w} (f : A ⊢ B) (g : B ⊢ C)
  → √l-map {w = w} (g ∘g f) ≡ √l-map {w = w} g ∘g √l-map {w = w} f
√l-map-seq {w = w} f g =
  ⊕≡ _ _
    ( ⊕-βl _ _
      ∙ cong (inl ∘g_) (sym ⊗-intro⊗-intro)
      ∙ sym (cong (_∘g (id ,⊗ f)) (⊕-βl _ _))
      ∙ cong (√l-map {w = w} g ∘g_) (sym (⊕-βl _ _)) )
    ( ⊕-βr _ _
      ∙ sym (⊕-βr _ _)
      ∙ cong (√l-map {w = w} g ∘g_) (sym (⊕-βr _ _)) )

map□-id : map□ (id {A = A}) ≡ id
map□-id = &ᴰ≡ _ _ λ w → cong (_∘g π w) (√l-map-id {w = w})

map□-seq : (f : A ⊢ B) (g : B ⊢ C) → map□ (g ∘g f) ≡ map□ g ∘g map□ f
map□-seq f g = &ᴰ≡ _ _ λ w → cong (_∘g π w) (√l-map-seq {w = w} f g)

------------------------------------------------------------------------------
-- Naturality of the counit √l-ε
------------------------------------------------------------------------------

√l-ε-nat : (f : A ⊢ B) → f ∘g √l-ε ≡ √l-ε ∘g √l-map {w = []} f
√l-ε-nat {A = A} {B = B} f =
  ⊕≡ _ _
    ( cong (f ∘g_) (⊕-βl _ _)
      ∙ ⊗-unit-l⊗-intro f
      ∙ sym (cong (_∘g (id ,⊗ f)) (⊕-βl _ _))
      ∙ cong (√l-ε ∘g_) (sym (⊕-βl _ _)) )
    ( cong (f ∘g_) (⊕-βr _ _)
      ∙ cong (_∘g ¬Start[]→⊥) (⊥-η (f ∘g ⊥-elim) ⊥-elim)
      ∙ sym (⊕-βr _ _)
      ∙ cong (√l-ε ∘g_) (sym (⊕-βr _ _)) )

------------------------------------------------------------------------------
-- `Start w ⊕ ¬Start w` is UNAMBIGUOUS (subterminal): any two LambekD maps into it
-- agree.  Captured INTERNALLY via the `unambiguous` predicate and its closure
-- combinators (no `isProp`-on-fibers reasoning):
--   • `Start w = ⌈w⌉⊗⊤` is unambiguous — the ⌈w⌉-prefix pins the split;
--   • `¬Start w = Start w ⇒ ⊥` is unambiguous — an exponential into ⊥;
--   • the summands are disjoint — `Start w & ¬Start w ⊢ ⊥` by ⇒-app.
-- This is the handle that forces every `dec-Start` decision to be canonical.
------------------------------------------------------------------------------

unambiguous-Start : ∀ w → unambiguous (Start w)
unambiguous-Start w = isLang→unambiguous isLang-Start
  where
    opaque
      unfolding _⊗_ ⊤ same-parses the-split
      isLang-Start : isLang (Start w)
      isLang-Start u p q =
        ⊗≡ {A = ⌈ w ⌉} {B = ⊤} {w = u} p q
          (unique-splitting-⌈⌉L w u p q)
          (ΣPathP ( isProp→PathP (λ i → isLang⌈⌉ w _) _ _
                  , isProp→PathP (λ i → isPropUnit) _ _ ))

unambiguous-¬Start : ∀ w → unambiguous (¬Start w)
unambiguous-¬Start w = unambiguous⇒ unambiguous⊥

disjoint-Start : ∀ w → disjoint (Start w) (¬Start w)
disjoint-Start w = ⇒-app ∘g &-swap

-- subterminality: any two LambekD maps into the decision sum coincide.
unambiguous-Dec : ∀ w → unambiguous (Start w ⊕ ¬Start w)
unambiguous-Dec w =
  unambiguous⊕ (unambiguous-Start w) (unambiguous-¬Start w) (disjoint-Start w)

-- &⊕-distR on a known branch.
private
  variable
    ℓD : Level
    D : Grammar ℓD

opaque
  unfolding ⇒-app ⇒-intro ⊕-elim _⊕_ _&_ &-intro π₁ π₂ inl inr
  &⊕-distR-inl : ∀ {ℓE ℓC'} {E : Grammar ℓE} {C : Grammar ℓC'}
    (m : E ⊢ A) (n : E ⊢ C)
    → &⊕-distR {A = A} {B = B} {C = C} ∘g &-intro (inl ∘g m) n
      ≡ inl ∘g &-intro m n
  &⊕-distR-inl m n = refl

  &⊕-distR-inr : ∀ {ℓE ℓC'} {E : Grammar ℓE} {C : Grammar ℓC'}
    (m : E ⊢ B) (n : E ⊢ C)
    → &⊕-distR {A = A} {B = B} {C = C} ∘g &-intro (inr ∘g m) n
      ≡ inr ∘g &-intro m n
  &⊕-distR-inr m n = refl

opaque
  unfolding _&_ &-intro
  &-intro∘g : ∀ {ℓZ ℓW} {Z : Grammar ℓZ} {W : Grammar ℓW}
    (a : Z ⊢ A) (b : Z ⊢ B) (h : W ⊢ Z)
    → &-intro a b ∘g h ≡ &-intro (a ∘g h) (b ∘g h)
  &-intro∘g a b h = refl

-- push a postcomposition through a binary sum-elim.
⊕-elim-precomp : ∀ {ℓE ℓD'} {E : Grammar ℓE} {D' : Grammar ℓD'}
  (h : C ⊢ D') (a : A ⊢ C) (b : E ⊢ C)
  → h ∘g ⊕-elim a b ≡ ⊕-elim (h ∘g a) (h ∘g b)
⊕-elim-precomp h a b =
  ⊕≡ _ _
    (cong (h ∘g_) (⊕-βl a b) ∙ sym (⊕-βl (h ∘g a) (h ∘g b)))
    (cong (h ∘g_) (⊕-βr a b) ∙ sym (⊕-βr (h ∘g a) (h ∘g b)))

-- Eq.transport as a cubical transport-filler over eqToPath.
eqTransportFiller :
  ∀ {ℓ ℓ'} {Y : Type ℓ} {a b : Y} (P : Y → Type ℓ')
  → (p : a Eq.≡ b) (x : P a)
  → PathP (λ i → P (eqToPath p i)) x (Eq.transport P p x)
eqTransportFiller P Eq.refl x = refl

-- An `Eq.transport` along the residual self-equality is the identity.  The
-- proof term is the distributor's internal (`Tiny.chain`, not nameable here) and
-- the split is definitionally fixed, so we cannot J/refl-match it; instead the
-- residual self-loop `eqToPath p : rest ≡ rest` is refl since `String` is a set.
Eq-transport-loop : ∀ {ℓ'} {a : String} (P : String → Type ℓ')
  (p : a Eq.≡ a) (v : P a) → Eq.transport P p v ≡ v
Eq-transport-loop {a = a} P p v =
  sym (subst (λ q → PathP (λ i → P (q i)) v (Eq.transport P p v))
             (isSetString a a (eqToPath p) refl)
             (eqTransportFiller P p v))

-- Section of the indexed prefix-distributor: distributing the ⌈ w ⌉ factor over
-- a `&ᴰ` (⊤-anchor from the same element) and recombining is the identity.
opaque
  unfolding ⌈⌉-⊗&ᴰ-distL⁻Eq _⊗_ _&_ &-intro π₂ ⊤ ⊤-intro same-parses the-split
  distL-roundtrip : ∀ {ℓX' ℓ'} {X : Type ℓX'} {B : X → Grammar ℓ'} {w}
    → ⌈⌉-⊗&ᴰ-distL⁻Eq {w = w} {A = B}
        ∘g &-intro (id ,⊗ ⊤-intro) (&ᴰ-intro (λ x → id ,⊗ π x))
      ≡ id {A = ⌈ w ⌉ ⊗ (&[ x ∈ X ] B x)}
  distL-roundtrip {X = X} {B = B} {w = w} = funExt λ u → funExt λ e →
    ⊗≡ {A = ⌈ w ⌉} {B = &[ x ∈ X ] B x} {w = u} _ _ refl
      (ΣPathP ( refl
              , funExt λ x → Eq-transport-loop (B x) _ (e .snd .snd x) ))

-- the section of √l-dist (its candidate inverse): project each component.
√undist : ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA}
  → √l-string w (&[ x ∈ X ] B x) ⊢ &[ x ∈ X ] √l-string w (B x)
√undist {w = w} = &ᴰ-intro (λ x → √l-map {w = w} (π x))

------------------------------------------------------------------------------
-- Index cast for √l-string along an Eq-path of prefixes, and its π-coherence.
------------------------------------------------------------------------------

√l-castEq : ∀ {ℓC} {C : Grammar ℓC} {w w'} → w' Eq.≡ w → √l-string w' C ⊢ √l-string w C
√l-castEq {C = C} e u d = Eq.transport (λ z → √l-string z C u) e d

castπ : ∀ {w w'} (e : w' Eq.≡ w)
  → √l-castEq {C = A} e ∘g π {A = λ z → √l-string z A} w' ≡ π w
castπ Eq.refl = refl

-- ⌈ w ⌉ is unambiguous (a summand of the unambiguous ⊕[w] ⌈w⌉).
unambiguous-⌈⌉ : ∀ w → unambiguous ⌈ w ⌉
unambiguous-⌈⌉ w =
  unambiguous⊕ᴰ {A = λ w' → ⌈ w' ⌉} isSetString unambiguous⊕⌈⌉ w

-- ⌈⌉-only index cast.
castEq⌈⌉ : ∀ {w w'} → w' Eq.≡ w → ⌈ w' ⌉ ⊢ ⌈ w ⌉
castEq⌈⌉ e u d = Eq.transport (λ z → ⌈ z ⌉ u) e d

-- MacLane triangle (plain ε): collapse an ε prepended on the left factor.
-- Derived algebraically from ⊗-assoc⊗-unit-l⁻ + unit cancellations.
tri2 : ∀ {ℓB'} {Bg : Grammar ℓB'}
  → (id ,⊗ ⊗-unit-l) ∘g ⊗-assoc⁻ {A = A} {B = ε} {C = Bg}
    ≡ ⊗-unit-r ,⊗ id
tri2 {A = A} {Bg = Bg} = sym
  ( cong (_∘g (⊗-unit-r ,⊗ id)) (sym aux)
  ∙ cong (((id ,⊗ ⊗-unit-l) ∘g ⊗-assoc⁻) ∘g_) cancel )
  where
    cancel : (⊗-unit-r⁻ ,⊗ id) ∘g (⊗-unit-r {A = A} ,⊗ id) ≡ id
    cancel = ⊗-intro⊗-intro ∙ cong (_,⊗ id) ⊗-unit-rr⁻ ∙ id,⊗id≡id
    aux : (id ,⊗ ⊗-unit-l) ∘g ⊗-assoc⁻ {A = A} {B = ε} {C = Bg}
            ∘g (⊗-unit-r⁻ ,⊗ id) ≡ id
    aux =
        cong ((id ,⊗ ⊗-unit-l) ∘g_)
             ( cong (⊗-assoc⁻ ∘g_) (sym ⊗-assoc⊗-unit-l⁻)
             ∙ cong (_∘g (id ,⊗ ⊗-unit-l⁻)) ⊗-assoc⁻∘⊗-assoc≡id )
      ∙ ⊗-intro⊗-intro
      ∙ cong (id ,⊗_) ⊗-unit-l⁻l
      ∙ id,⊗id≡id

-- √l-string cast on the inl summand factors as the ⌈⌉-cast on the prefix.
castEqA-factor : ∀ {w w'} (e : w' Eq.≡ w)
  → √l-castEq {C = A} e ∘g inl
    ≡ inl {B = ¬Start w} ∘g (castEq⌈⌉ e ,⊗ id)
castEqA-factor Eq.refl = cong (inl ∘g_) (sym id,⊗id≡id)

-- ¬Start index cast, and the √l-string cast on the inr summand.
castEq¬ : ∀ {w w'} → w' Eq.≡ w → ¬Start w' ⊢ ¬Start w
castEq¬ e u d = Eq.transport (λ z → ¬Start z u) e d

castEqA-factor-inr : ∀ {w w'} (e : w' Eq.≡ w)
  → √l-castEq {C = A} e ∘g inr
    ≡ inr {B = ⌈ w ⌉ ⊗ A} ∘g castEq¬ e
castEqA-factor-inr Eq.refl = refl

-- ⌈⌉-split is a section of ⌈⌉-++ (induction on the first prefix).
⌈⌉-split-++ : ∀ w v → ⌈⌉-split w v ∘g ⌈⌉-++ w v ≡ id {A = ⌈ w ⌉ ⊗ ⌈ v ⌉}
⌈⌉-split-++ [] v = ⊗-unit-ll⁻
⌈⌉-split-++ (c ∷ w) v =
    cong (λ z → ⊗-assoc ∘g z ∘g ⊗-assoc⁻)
         (⊗-intro⊗-intro ∙ cong (id ,⊗_) (⌈⌉-split-++ w v) ∙ id,⊗id≡id)
  ∙ ⊗-assoc∘⊗-assoc⁻≡id

-- ⌈w⌉⊗(⌈v⌉⊗⌈u⌉) is unambiguous: it is a retract of the unambiguous ⌈w++(v++u)⌉.
unambiguous-⌈⌉³ : ∀ w v u → unambiguous (⌈ w ⌉ ⊗ (⌈ v ⌉ ⊗ ⌈ u ⌉))
unambiguous-⌈⌉³ w v u =
  isUnambiguousRetract'
    (⌈⌉-++ w (v ++ u) ∘g (id ,⊗ ⌈⌉-++ v u))
    ((id ,⊗ ⌈⌉-split v u) ∘g ⌈⌉-split w (v ++ u))
    ( cong (λ z → (id ,⊗ ⌈⌉-split v u) ∘g z ∘g (id ,⊗ ⌈⌉-++ v u))
           (⌈⌉-split-++ w (v ++ u))
    ∙ (⊗-intro⊗-intro ∙ cong (id ,⊗_) (⌈⌉-split-++ v u) ∙ id,⊗id≡id) )
    (unambiguous-⌈⌉ (w ++ (v ++ u)))

-- ⌈⌉-split ASSOCIATIVITY (the geometric core of the pentagon): both legs are maps
-- into the unambiguous ⌈w⌉⊗(⌈v⌉⊗⌈u⌉), so they agree on the nose.
⌈⌉-split-assoc : ∀ {w v u}
  → ⊗-assoc⁻ ∘g (⌈⌉-split w v ,⊗ id) ∘g ⌈⌉-split (w ++ v) u
    ≡ (id ,⊗ ⌈⌉-split v u) ∘g ⌈⌉-split w (v ++ u) ∘g castEq⌈⌉ (++-assoc-Eq w v u)
⌈⌉-split-assoc {w} {v} {u} = unambiguous-⌈⌉³ w v u _ _


-- inverse MacLane pentagon for ⊗-assoc⁻, derived from ⊗-pentagon by inverting the
-- two associator isos (L ≡ R ⟹ R⁻¹ ≡ L⁻¹).
private
  variable
    ℓA' ℓB' ℓC' ℓD' : Level
pentagon⁻ : ∀ {A : Grammar ℓA'} {Bg : Grammar ℓB'}
              {Cg : Grammar ℓC'} {Dg : Grammar ℓD'}
  → ⊗-assoc⁻ {A = A} {B = Bg} {C = Cg ⊗ Dg} ∘g ⊗-assoc⁻ {A = A ⊗ Bg} {B = Cg} {C = Dg}
    ≡ (id ,⊗ ⊗-assoc⁻ {A = Bg} {B = Cg} {C = Dg})
      ∘g ⊗-assoc⁻ {A = A} {B = Bg ⊗ Cg} {C = Dg}
      ∘g (⊗-assoc⁻ {A = A} {B = Bg} {C = Cg} ,⊗ id)
pentagon⁻ {A = A} {Bg = Bg} {Cg = Cg} {Dg = Dg} =
    sym (cong (R⁻¹ ∘g_) L∘L⁻¹)
  ∙ cong (λ z → R⁻¹ ∘g z ∘g L⁻¹) ⊗-pentagon
  ∙ cong (_∘g L⁻¹) R⁻¹∘R
  where
    R⁻¹ = ⊗-assoc⁻ {A = A} {B = Bg} {C = Cg ⊗ Dg} ∘g ⊗-assoc⁻ {A = A ⊗ Bg} {B = Cg} {C = Dg}
    L⁻¹ = (id ,⊗ ⊗-assoc⁻ {A = Bg} {B = Cg} {C = Dg})
            ∘g ⊗-assoc⁻ {A = A} {B = Bg ⊗ Cg} {C = Dg}
            ∘g (⊗-assoc⁻ {A = A} {B = Bg} {C = Cg} ,⊗ id)
    R⁻¹∘R : R⁻¹ ∘g (⊗-assoc ∘g ⊗-assoc) ≡ id
    R⁻¹∘R =
        cong (λ z → ⊗-assoc⁻ ∘g z ∘g ⊗-assoc) ⊗-assoc⁻∘⊗-assoc≡id
      ∙ ⊗-assoc⁻∘⊗-assoc≡id
    L∘L⁻¹ :
      (⊗-intro (⊗-assoc {A = A}) id ∘g ⊗-assoc
        ∘g ⊗-intro id (⊗-assoc {A = Bg} {B = Cg} {C = Dg})) ∘g L⁻¹ ≡ id
    L∘L⁻¹ =
        cong (λ z → (⊗-assoc ,⊗ id) ∘g ⊗-assoc ∘g z
                    ∘g ⊗-assoc⁻ ∘g (⊗-assoc⁻ ,⊗ id))
             (⊗-intro⊗-intro ∙ cong (id ,⊗_) ⊗-assoc∘⊗-assoc⁻≡id ∙ id,⊗id≡id)
      ∙ cong (λ z → (⊗-assoc ,⊗ id) ∘g z ∘g (⊗-assoc⁻ ,⊗ id)) ⊗-assoc∘⊗-assoc⁻≡id
      ∙ (⊗-intro⊗-intro ∙ cong (_,⊗ id) ⊗-assoc∘⊗-assoc⁻≡id ∙ id,⊗id≡id)

-- forget the carried data, keeping only the Start/¬Start decision.
forget-dec : ∀ {ℓC} {C : Grammar ℓC} {w} → √l-string w C ⊢ Start w ⊕ ¬Start w
forget-dec = ⊕-elim (inl ∘g (id ,⊗ ⊤-intro)) inr

-- Generic mono-from-retract: if `r ∘g s ≡ id`, then `s` is monic.
mono-by-retract : ∀ {ℓx ℓy ℓz} {X : Grammar ℓx} {Y : Grammar ℓy} {Z : Grammar ℓz}
  (r : Y ⊢ X) (s : X ⊢ Y) → r ∘g s ≡ id
  → (g₁ g₂ : Z ⊢ X) → s ∘g g₁ ≡ s ∘g g₂ → g₁ ≡ g₂
mono-by-retract r s ret g₁ g₂ hyp =
    sym (cong (_∘g g₁) ret) ∙ cong (r ∘g_) hyp ∙ cong (_∘g g₂) ret

module _ (disc : Discrete ⟨ Alphabet ⟩) where

  -- with `Start w` in hand, the x-component must be on its prefix branch.
  prefix-of : ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA} (x : X)
    → (Start w & (&[ x' ∈ X ] √l-string w (B x'))) ⊢ ⌈ w ⌉ ⊗ B x
  prefix-of x =
    ⊕-elim π₁ (⊥-elim ∘g ⇒-app)
    ∘g &⊕-distR
    ∘g &-intro (π x ∘g π₂) π₁

  -- the two branches of √l-dist (named so the section/proj proofs can use them).
  Binl : ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA}
    → (Start w & (&[ x ∈ X ] √l-string w (B x))) ⊢ √l-string w (&[ x ∈ X ] B x)
  Binl {w = w} {X = X} {B = B} =
    inl ∘g ⌈⌉-⊗&ᴰ-distL⁻Eq {w = w} {A = B}
        ∘g &-intro π₁ (&ᴰ-intro (prefix-of {w = w} {X = X} {B = B}))

  Binr : ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA}
    → (¬Start w & (&[ x ∈ X ] √l-string w (B x))) ⊢ √l-string w (&[ x ∈ X ] B x)
  Binr = inr ∘g π₁

  -- Distribute √l-string over an indexed product.  DECIDE `Start w`:
  --   • Start w  : every component is on its prefix branch (the ¬Start w branch
  --     is killed by Start w & ¬Start w ⊢ ⊥), so pull the common ⌈w⌉ out with
  --     the indexed prefix-distributor `⌈⌉-⊗&ᴰ-distL⁻Eq`.
  --   • ¬Start w : answer ¬Start w directly.
  √l-dist :
    ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA} →
    (&[ x ∈ X ] √l-string w (B x)) ⊢ √l-string w (&[ x ∈ X ] B x)
  √l-dist {w = w} {X = X} {B = B} =
    ⊕-elim (Binl {w = w} {X = X} {B = B}) (Binr {w = w} {X = X} {B = B})
    ∘g &⊕-distR
    ∘g &-intro (dec-Start disc w ∘g ⊤-intro) id

  -- the OTHER iso direction: projecting a component after √l-dist is projecting
  -- it first.  Rewrite √l-dist's decision (subterminal) to come from the
  -- x-component itself, then case on that component.
  √l-dist-proj : ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA} (x : X)
    → √l-map {w = w} (π x) ∘g √l-dist {w = w} {X = X} {B = B}
      ≡ π {A = λ x → √l-string w (B x)} x
  √l-dist-proj {w = w} {X = X} {B = B} x =
    cong (λ d → √l-map {w = w} (π x)
                  ∘g ⊕-elim (Binl {w = w} {X = X} {B = B}) (Binr {w = w} {X = X} {B = B})
                  ∘g &⊕-distR ∘g &-intro d id)
         (unambiguous-Dec w (dec-Start disc w ∘g ⊤-intro)
                          (forget-dec {C = B x} {w = w} ∘g π x))
    ∙ proj-pointwise
    where
      proj-pointwise :
        √l-map {w = w} (π x)
          ∘g ⊕-elim (Binl {w = w} {X = X} {B = B}) (Binr {w = w} {X = X} {B = B})
          ∘g &⊕-distR ∘g &-intro (forget-dec {C = B x} {w = w} ∘g π x) id
        ≡ π {A = λ x → √l-string w (B x)} x
      proj-pointwise = funExt λ u → funExt λ F → proj-pt u F
        where
        opaque
          unfolding ⌈⌉-⊗&ᴰ-distL⁻Eq _⊗_ _&_ &-intro π₁ π₂ ⊤ ⊤-intro
                    same-parses the-split ⊕-elim _⊕_ inl inr
                    ⇒-app ⇒-intro _⇒_
          proj-pt : ∀ u (F : (&[ x ∈ X ] √l-string w (B x)) u)
            → (√l-map {w = w} (π x)
                 ∘g ⊕-elim (Binl {w = w} {X = X} {B = B}) (Binr {w = w} {X = X} {B = B})
                 ∘g &⊕-distR ∘g &-intro (forget-dec {C = B x} {w = w} ∘g π x) id) u F
              ≡ π {A = λ x → √l-string w (B x)} x u F
          proj-pt u F with F x in eq
          ... | Sum.inl p rewrite eq =
                  cong (Sum.inl {B = ¬Start w u})
                       (ΣPathP (refl , ΣPathP (refl ,
                          Eq-transport-loop (B x) _ (p .snd .snd))))
          ... | Sum.inr q = refl

  -- comultiplication
  δ : □ A ⊢ □ (□ A)
  δ = &ᴰ-intro λ w →
        √l-dist {w = w}
        ∘g &ᴰ-intro λ v → √l-cat disc {w = w} {v = v} ∘g π (w ++ v)

  -- √l-dist is split epi with section √undist.
  --   ⊕≡ on the source `√l-string w (&ᴰ B)`:
  --   • inl (⌈w⌉⊗&ᴰ B): the decision is Start w (subterminal), &⊕-distR-inl picks
  --     the prefix branch, each `prefix-of` recovers `id ,⊗ π x`, and the
  --     distributor section `distL-roundtrip` collapses it to id.
  --   • inr (¬Start w): the decision is ¬Start w (subterminal), &⊕-distR-inr
  --     picks the no-prefix branch, which is the identity inr.
  √l-dist-section : ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA}
    → √l-dist {w = w} {X = X} {B = B} ∘g √undist {w = w} {B = B} ≡ id
  √l-dist-section {w = w} {X = X} {B = B} =
    ⊕≡ (√l-dist {w = w} {X = X} {B = B} ∘g √undist {w = w} {B = B}) id
       inlCase inrCase
    where
      U : (⌈ w ⌉ ⊗ (&[ x ∈ X ] B x)) ⊢ &[ x ∈ X ] √l-string w (B x)
      U = √undist {w = w} {B = B} ∘g inl

      Un : ¬Start w ⊢ &[ x ∈ X ] √l-string w (B x)
      Un = √undist {w = w} {B = B} ∘g inr

      Binl' : (Start w & (&[ x ∈ X ] √l-string w (B x))) ⊢ √l-string w (&[ x ∈ X ] B x)
      Binl' = Binl {w = w} {X = X} {B = B}

      Binr' : (¬Start w & (&[ x ∈ X ] √l-string w (B x))) ⊢ √l-string w (&[ x ∈ X ] B x)
      Binr' = Binr {w = w} {X = X} {B = B}

      -- each prefix-of recovers `id ,⊗ π x` from the Start-w'd all-inl family.
      prefix-of-roundtrip : ∀ x
        → prefix-of {w = w} {B = B} x ∘g &-intro (id ,⊗ ⊤-intro) U
          ≡ (id ,⊗ π x)
      prefix-of-roundtrip x =
          cong (λ z → ⊕-elim π₁ (⊥-elim ∘g ⇒-app) ∘g &⊕-distR ∘g z)
               ( &-intro∘g (π x ∘g π₂) π₁ (&-intro (id ,⊗ ⊤-intro) U)
               ∙ cong₂ &-intro
                   (cong (π x ∘g_) (&-β₂ _ _) ∙ ⊕-βl _ _)
                   (&-β₁ _ _) )
        ∙ cong (⊕-elim π₁ (⊥-elim ∘g ⇒-app) ∘g_)
               (&⊕-distR-inl {B = ¬Start w} (id ,⊗ π x) (id ,⊗ ⊤-intro))
        ∙ cong (_∘g &-intro (id ,⊗ π x) (id ,⊗ ⊤-intro))
               (⊕-βl π₁ (⊥-elim ∘g ⇒-app))
        ∙ &-β₁ (id ,⊗ π x) (id ,⊗ ⊤-intro)

      inlCase :
        (√l-dist {w = w} {B = B} ∘g √undist {w = w} {B = B}) ∘g inl ≡ inl
      inlCase =
          cong (λ z → ⊕-elim Binl' Binr' ∘g &⊕-distR ∘g z)
               (&-intro∘g (dec-Start disc w ∘g ⊤-intro) id U)
        ∙ cong (λ z → ⊕-elim Binl' Binr' ∘g &⊕-distR ∘g &-intro z U)
               (unambiguous-Dec w ((dec-Start disc w ∘g ⊤-intro) ∘g U)
                                (inl ∘g (id ,⊗ ⊤-intro)))
        ∙ cong (⊕-elim Binl' Binr' ∘g_) (&⊕-distR-inl {B = ¬Start w} (id ,⊗ ⊤-intro) U)
        ∙ cong (_∘g &-intro (id ,⊗ ⊤-intro) U) (⊕-βl Binl' Binr')
        ∙ cong (λ z → inl ∘g ⌈⌉-⊗&ᴰ-distL⁻Eq {w = w} {A = B} ∘g z)
               ( &-intro∘g π₁ (&ᴰ-intro (prefix-of {w = w} {X = X} {B = B}))
                   (&-intro (id ,⊗ ⊤-intro) U)
               ∙ cong₂ &-intro (&-β₁ _ _) (&ᴰ≡ _ _ λ x → prefix-of-roundtrip x) )
        ∙ cong (inl {B = ¬Start w} ∘g_) distL-roundtrip

      inrCase :
        (√l-dist {w = w} {B = B} ∘g √undist {w = w} {B = B}) ∘g inr ≡ inr
      inrCase =
          cong (λ z → ⊕-elim Binl' Binr' ∘g &⊕-distR ∘g z)
               (&-intro∘g (dec-Start disc w ∘g ⊤-intro) id Un)
        ∙ cong (λ z → ⊕-elim Binl' Binr' ∘g &⊕-distR ∘g &-intro z Un)
               (unambiguous-Dec w ((dec-Start disc w ∘g ⊤-intro) ∘g Un)
                                (inr {A = ¬Start w} {B = Start w}))
        ∙ cong (⊕-elim Binl' Binr' ∘g_) (&⊕-distR-inr {A = Start w} id Un)
        ∙ cong (_∘g &-intro id Un) (⊕-βr Binl' Binr')
        ∙ cong (inr {A = ¬Start w} {B = ⌈ w ⌉ ⊗ (&[ x ∈ X ] B x)} ∘g_)
               (&-β₁ id Un)

  ------------------------------------------------------------------------------
  -- √l-cat coherences (naturality, counits, pentagon).
  ------------------------------------------------------------------------------

  -- naturality of √l-cat in the grammar argument.  Pointwise: on the prefix
  -- branch both sides repackage the (split, ⌈w⌉, ⌈v⌉, A) tuple identically with
  -- f threaded onto the deep A; on the no-prefix branch f is ignored (inr).
  opaque
    unfolding √l-cat _⊗_ ⊗-intro ⊗-assoc⁻ _⊕_ inl inr ⊕-elim &⊕-distR &-intro
              π₁ π₂ ⌈⌉-split same-parses the-split ⊤ ⊤-intro ⇒-app ⇒-intro _⇒_
    √l-cat-nat : ∀ {ℓA' ℓB'} {A : Grammar ℓA'} {B : Grammar ℓB'} {w v : String}
      (f : A ⊢ B)
      → √l-cat disc {A = B} {w = w} {v = v} ∘g √l-map {w = w ++ v} f
        ≡ √l-map {w = w} (√l-map {w = v} f) ∘g √l-cat disc {A = A} {w = w} {v = v}
    √l-cat-nat {A = A} {B = B} {w = w} {v = v} f =
      ⊕≡ _ _
        -- prefix branch: pure ⊗-repackaging, refl after unfolding.
        (funExt λ u → funExt λ s → refl)
        -- no-prefix branch: the Start-w decision is SHARED and untouched; we only
        -- push √l-map{w}(√l-map{v}f) through the no-prefix ⊕-elim (⊕-elim-precomp).
        -- Each branch then threads f onto a ¬Start v / ¬Start w, which √l-map sees
        -- as `inr` (no A-content), so the pushed branches are defeq to the B-ones.
        (sym (cong (_∘g Ddec) (⊕-elim-precomp g b1 b2)))
      where
        g : √l-string w (√l-string v A) ⊢ √l-string w (√l-string v B)
        g = √l-map {w = w} (√l-map {w = v} f)
        Ddec : ¬Start (w ++ v)
            ⊢ (Start w & ¬Start (w ++ v)) ⊕ (¬Start w & ¬Start (w ++ v))
        Ddec = &⊕-distR ∘g &-intro (dec-Start disc w ∘g ⊤-intro) id
        b1 : (Start w & ¬Start (w ++ v)) ⊢ √l-string w (√l-string v A)
        b1 = inl ∘g (id ,⊗ inr) ∘g Start&¬Start-cat w v
        b2 : (¬Start w & ¬Start (w ++ v)) ⊢ √l-string w (√l-string v A)
        b2 = inr ∘g π₁

  -- left counit of √l-cat: peeling [] (via √l-ε) undoes a √l-cat at depth [].
  opaque
    unfolding √l-cat √l-ε _⊗_ ⊗-intro ⊗-assoc⁻ ⊗-unit-l ⊗-unit-l⁻ _⊕_ inl inr
              ⊕-elim &⊕-distR &-intro π₁ π₂ ⌈⌉-split same-parses the-split
              ⊤ ⊤-intro ⇒-app ⇒-intro _⇒_ Start&¬Start-cat
    √l-cat-ε : ∀ {v} → √l-ε ∘g √l-cat disc {A = A} {w = []} {v = v} ≡ id
    √l-cat-ε {A = A} {v = v} =
      ⊕≡ _ _
        -- prefix branch (⌈v⌉⊗A): inside the opaque block `√l-ε ∘ √l-cat ∘ inl` is
        -- defeq to `⊗-unit-l ∘ (id,⊗inl) ∘ ⊗-assoc⁻ ∘ (⊗-unit-l⁻ ,⊗ id)`; ⊗-unit-l
        -- naturality pulls inl out front and the MacLane triangle collapses the rest.
        ( cong (_∘g (⊗-assoc⁻ ∘g (⊗-unit-l⁻ ,⊗ id)))
               (sym (⊗-unit-l⊗-intro (inl {A = ⌈ v ⌉ ⊗ A} {B = ¬Start v})))
        ∙ cong (inl {A = ⌈ v ⌉ ⊗ A} {B = ¬Start v} ∘g_) triangle )
        -- no-prefix branch (¬Start v): dec-Start [] is canonically Start [], so we
        -- land in the inl summand and √l-ε strips the ε; the `Eq.transport` self-loop
        -- vanishes and the rebuilt ¬Start v agrees with q (¬Start v is unambiguous).
        (funExt λ u → funExt λ q →
          Eq-transport-loop (√l-string v A) _ _
          ∙ cong Sum.inr (unambiguous→isLang (unambiguous-¬Start v) u _ q))
      where
        triangle : ⊗-unit-l ∘g ⊗-assoc⁻ ∘g (⊗-unit-l⁻ ,⊗ id)
                   ≡ id {A = ⌈ v ⌉ ⊗ A}
        triangle = funExt λ u → funExt λ where
          (((l , r) , Eq.refl) , p⌈⌉ , pA) → refl

  -- right counit of √l-cat: peeling w then [] (dropping the []-peel via √l-ε) is
  -- the w-peel, up to the index cast √l-castEq (w ++ [] ≡ w).
  opaque
    unfolding √l-cat √l-ε _⊗_ ⊗-intro ⊗-assoc⁻ ⊗-unit-l ⊗-unit-l⁻ ⊗-unit-r
              _⊕_ inl inr ⊕-elim &⊕-distR &-intro π₁ π₂ ⌈⌉-split
              same-parses the-split ⊤ ⊤-intro ⇒-app ⇒-intro _⇒_ Start&¬Start-cat
    √l-cat-εr : ∀ {w} → √l-map {w = w} √l-ε ∘g √l-cat disc {A = A} {w = w} {v = []}
                ≡ √l-castEq {C = A} (++-unit-r-Eq w)
    √l-cat-εr {A = A} {w = w} = ⊕≡ _ _
      -- prefix branch: ⌈⌉-split peels the trailing ε, √l-ε strips it (tri2 collapses
      -- the ε via ⊗-unit), and `⌈w⌉` unambiguous identifies the residual ⌈⌉-cast.
      ( cong (inl {A = ⌈ w ⌉ ⊗ A} {B = ¬Start w} ∘g_) h-eq
      ∙ sym (castEqA-factor {A = A} (++-unit-r-Eq w)) )
      -- no-prefix branch: the input ¬Start(w++[]) forces the Start-w decision to
      -- the ¬Start branch (unambiguous-Dec), so the whole composite routes through
      -- `inr` and is the ¬Start-cast; no decision casing, no vacuous Start branch.
      ( cong (λ d → √l-map {w = w} √l-ε
                    ∘g ⊕-elim b1 b2 ∘g &⊕-distR ∘g &-intro d id)
             (unambiguous-Dec w (dec-Start disc w ∘g ⊤-intro)
                                (inr ∘g castEq¬ (++-unit-r-Eq w)))
      ∙ sym (castEqA-factor-inr {A = A} (++-unit-r-Eq w)) )
      where
        b1 : (Start w & ¬Start (w ++ [])) ⊢ √l-string w (√l-string [] A)
        b1 = inl ∘g (id ,⊗ inr) ∘g Start&¬Start-cat w []
        b2 : (¬Start w & ¬Start (w ++ [])) ⊢ √l-string w (√l-string [] A)
        b2 = inr ∘g π₁
        h-eq : (id ,⊗ ⊗-unit-l) ∘g ⊗-assoc⁻ ∘g (⌈⌉-split w [] ,⊗ id {A = A})
               ≡ (castEq⌈⌉ (++-unit-r-Eq w) ,⊗ id {A = A})
        h-eq =
            cong (_∘g (⌈⌉-split w [] ,⊗ id {A = A})) (tri2 {A = ⌈ w ⌉} {Bg = A})
          ∙ ⊗-intro⊗-intro {f = ⊗-unit-r {A = ⌈ w ⌉}} {f' = id {A = A}}
                           {f'' = ⌈⌉-split w []} {f''' = id {A = A}}
          ∙ cong (_,⊗ id {A = A})
                 (unambiguous-⌈⌉ w (⊗-unit-r ∘g ⌈⌉-split w [])
                                   (castEq⌈⌉ (++-unit-r-Eq w)))

  ------------------------------------------------------------------------------
  -- Comonad laws.
  ------------------------------------------------------------------------------

  -- left counit:  ε□ ∘g δ ≡ id.  Per component v:
  --   π v ∘ ε□ ∘ δ
  --     = π v ∘ √l-ε ∘ √l-dist[] ∘ (λ v'. √l-cat[]v' ∘ π v')   [δ at []]
  --     = √l-ε ∘ √l-map (π v) ∘ √l-dist[] ∘ (...)               [√l-ε-nat]
  --     = √l-ε ∘ π v ∘ (...)                                    [√l-dist-proj]
  --     = √l-ε ∘ √l-cat[]v ∘ π v                                [&ᴰ β]
  --     = π v                                                   [√l-cat-ε]
  □-counit-l : ε□ ∘g δ ≡ id {A = □ A}
  □-counit-l {A = A} = &ᴰ≡ _ _ λ v →
      cong (_∘g (√l-dist {w = []} {B = λ z → √l-string z A}
                  ∘g &ᴰ-intro (λ v' → √l-cat disc {A = A} {w = []} {v = v'}
                                       ∘g π {A = λ z → √l-string z A} ([] ++ v'))))
           (√l-ε-nat (π {A = λ z → √l-string z A} v))
    ∙ cong (λ z → √l-ε ∘g z
                  ∘g &ᴰ-intro (λ v' → √l-cat disc {A = A} {w = []} {v = v'}
                                       ∘g π {A = λ z → √l-string z A} ([] ++ v')))
           (√l-dist-proj {w = []} {B = λ z → √l-string z A} v)
    ∙ cong (_∘g π {A = λ z → √l-string z A} v) (√l-cat-ε {A = A} {v = v})

  -- √l-dist is split epi (section √undist); hence √undist is monic.
  √l-undist-mono : ∀ {ℓ ℓX' ℓz} {X : Type ℓX'} {B : X → Grammar ℓ} {w}
    {Z : Grammar ℓz}
    (g₁ g₂ : Z ⊢ √l-string w (&[ x ∈ X ] B x))
    → √undist {w = w} {B = B} ∘g g₁ ≡ √undist {w = w} {B = B} ∘g g₂ → g₁ ≡ g₂
  √l-undist-mono {B = B} {w = w} =
    mono-by-retract (√l-dist {w = w} {B = B}) (√undist {w = w} {B = B})
      (√l-dist-section {w = w} {B = B})

  -- right counit:  map□ ε□ ∘g δ ≡ id.  Per component w:
  --   π w ∘ map□ ε□ ∘ δ
  --     = √l-map ε□ ∘ √l-dist[w] ∘ (λ v. √l-cat[w]v ∘ π(w++v))   [map□, δ]
  --     = √l-map √l-ε ∘ √l-map(π[]) ∘ √l-dist[w] ∘ (...)         [√l-map-seq]
  --     = √l-map √l-ε ∘ π[] ∘ (...)                              [√l-dist-proj]
  --     = √l-map √l-ε ∘ √l-cat[w][] ∘ π(w++[])                   [&ᴰ β]
  --     = √l-castEq(w++[]≡w) ∘ π(w++[])                          [√l-cat-εr]
  --     = π w                                                    [castπ]
  □-counit-r : map□ ε□ ∘g δ ≡ id {A = □ A}
  □-counit-r {A = A} = &ᴰ≡ _ _ λ w →
    let innerδ : □ A ⊢ &[ v ∈ String ] √l-string w (√l-string v A)
        innerδ = &ᴰ-intro (λ v → √l-cat disc {A = A} {w = w} {v = v}
                                ∘g π {A = λ z → √l-string z A} (w ++ v))
    in
      cong (λ z → z ∘g √l-dist {w = w} {B = λ z → √l-string z A} ∘g innerδ)
           (√l-map-seq {w = w} (π {A = λ z → √l-string z A} []) √l-ε)
    ∙ cong (λ z → √l-map {w = w} √l-ε ∘g z ∘g innerδ)
           (√l-dist-proj {w = w} {B = λ z → √l-string z A} [])
    ∙ cong (_∘g π {A = λ z → √l-string z A} (w ++ [])) (√l-cat-εr {A = A} {w = w})
    ∙ castπ (++-unit-r-Eq w)

  -- √l-cat PENTAGON (associativity of the suffix peel).
  opaque
    unfolding √l-cat √l-map _⊗_ ⊗-intro ⊗-assoc ⊗-assoc⁻ _⊕_ inl inr ⊕-elim
              &⊕-distR &-intro π₁ π₂ ⌈⌉-split same-parses the-split
              ⊤ ⊤-intro ⇒-app ⇒-intro _⇒_ Start&¬Start-cat
    √l-cat-assoc : ∀ {ℓC'} {C : Grammar ℓC'} {w v u : String}
      → √l-cat disc {A = √l-string u C} {w = w} {v = v}
          ∘g √l-cat disc {A = C} {w = w ++ v} {v = u}
        ≡ √l-map {w = w} (√l-cat disc {A = C} {w = v} {v = u})
          ∘g √l-cat disc {A = C} {w = w} {v = v ++ u}
          ∘g √l-castEq {C = C} (++-assoc-Eq w v u)
    -- The geometric core `⌈⌉-split-assoc` (above) is PROVEN by unambiguity of
    -- ⌈w⌉⊗(⌈v⌉⊗⌈u⌉).  Remaining mechanical ⊗-bookkeeping:
    -- inl: front-load the inl-injections (⊗-intro⊗-intro / ⊗-assoc⁻⊗-intro) so both
    --   legs become `inl∘(id,⊗inl)∘(id,⊗(id,⊗inl)) ∘ <pure ⌈⌉⊗C map>`; factor C out
    --   past the ⊗-assoc's (⊗-pentagon) as `<⌈⌉-map> ,⊗ id_C`; close with ⌈⌉-split-assoc.
    -- inr: rewrite both decisions (dec-Start (w++v), dec-Start w on the LHS;
    --   dec-Start w, dec-Start v on the RHS) via unambiguous-Dec, then route through inr.
    √l-cat-assoc {C = C} {w = w} {v = v} {u = u} =
      ⊕≡ _ _
        ( pointwise-inl
        ∙ sym (cong (λ m → √l-map {w = w} (√l-cat disc {A = C} {w = v} {v = u})
                           ∘g √l-cat disc {A = C} {w = w} {v = v ++ u} ∘g m)
                    (castEqA-factor {A = C} (++-assoc-Eq w v u))) )
        {!!}
      where
        pointwise-inl :
          (√l-cat disc {A = √l-string u C} {w = w} {v = v}
            ∘g √l-cat disc {A = C} {w = w ++ v} {v = u}) ∘g inl
          ≡ √l-map {w = w} (√l-cat disc {A = C} {w = v} {v = u})
            ∘g √l-cat disc {A = C} {w = w} {v = v ++ u}
            ∘g inl ∘g (castEq⌈⌉ (++-assoc-Eq w v u) ,⊗ id)
        -- both legs are now `Sum.inl`-headed (no outer transport); the residual C
        -- passes through and the ⌈⌉-witnesses are forced by isLang⌈⌉.  The remaining
        -- content is the nested ⊗-element path whose split-paths are the genuine
        -- pentagon ++-assoc reassociations (cf. ⊗-pentagon's `sym (++-assoc …)`),
        -- determinable by interactive refine.  [interactive ⊗-position-path step]
        -- Reduced (via interaction): both legs are `Sum.inl L` / `Sum.inl R` in
        -- ⌈w⌉⊗√l-string v(√l-string u C); the deepest C-element is SHARED (cval) and
        -- the ⌈⌉-witnesses are props (isLang⌈⌉).  What remains is the nested
        -- ⊗-element PathP whose split-paths are the genuine pentagon ++-assoc
        -- reassociations (cf. ⊗-pentagon's `sym (++-assoc …)`).  Structure:
        --   cong Sum.inl (⊗≡ _ _ (unique-splitting-⌈⌉L w …)
        --     (ΣPathP (isProp→PathP isLang⌈⌉ … , toPathP <transport-path>)))
        -- `toPathP` flattens the outer PathP cleanly; the transport-of-Sum.inl path
        -- recurses two more levels (⌈v⌉, ⌈u⌉) with position transports, and Agda
        -- cannot infer the 50-line stuck split elements without them supplied
        -- explicitly.  [remaining: nested transport/position-path bookkeeping]
        pointwise-inl =
          funExt λ z → funExt λ where
            (((pref , cpos) , Eq.refl) , ⌈⌉wit , cval) → {!!}
