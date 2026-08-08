{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE ELIMINATOR OF THE FREE MODEL, AND THE REINDEXING THEOREM.

  `Opt.agda` presents `TmG` as an ALGEBRA for a shape functor,

      StepG A = SoloG ⊕ ((A ⊛ A) ⊕ BodyOf A)
      roll    : StepG TmG ⊢ TmG
      foldTm  : (A : Ctx) → StepG A ⊢ A → TmG ⊢ A
      foldRollPass : foldTm TmG roll ≡ idPass

  -- i.e. it gives the RECURSOR (weak initiality) and one η-law.  That
  is enough to define passes and not enough to prove anything about
  them: a statement about a term needs a motive that MENTIONS the term,
  and every such proof in the tree (`Opt.foldRoll`, `Correct`'s
  `relFrame`/`relDelE`, `Equiv/Glue.relConvG`) spells the recursion out
  again locally.

  This file supplies the missing half, once:

      Ctxᴰ A ℓ  = (u : Usage) → A u → Type ℓ      a DISPLAYED grammar
      Algᴰ A α Aᴰ                                  a DISPLAYED algebra
      indTm : Algᴰ TmG roll Aᴰ → (u : Usage) (t : Tm u) → Aᴰ u t

  `indTm` is THE eliminator; `foldTm` is its instance at a motive that
  ignores the term (`foldD`/`fold≡`, exactly as `TheoryGrammar.Induction`
  relates `indμ` to `fold` for `μ`), and `foldRoll` and `foldUnique`
  both drop out of it with no further induction.

  THE REINDEXING THEOREM, and why it is what makes this usable.

  A displayed model is almost never written over `TmG` directly.  It is
  written over a TARGET model `(B, β)` -- the thing a pass compiles into
  -- as a family

      Bᴰ : (u : Usage) → Tm u → B u → Type ℓ

  relating a source term to its image, together with a displayed algebra
  over the PAIRED algebra on `TmG & B`.  `reindexPair` transports that
  along the paired interpretation

      pairFold B β : TmG ⊢ (TmG & B)        u t ↦ (t , foldTm B β u t)

  into a displayed algebra over `roll`, and `fundamental` is then the
  composite with `indTm`.  The transport costs NOTHING: `foldTm`'s three
  clauses ARE the algebra-map equations, so every clause of
  `reindexPair` is the target's own clause with its type silently
  reassociated -- no `subst`, no `Eq.transport`, nothing that could
  stall a `refl` test downstream.  (Compare `ChangeOfTheory`'s
  `reinterpretTerm`, which is `refl` for the same reason.)

  This is the c-c-l gluing recipe transcribed.  There

      logicalRelation = elimLocal Q pointwise Dⱽ generators
                      : Section (pointwise .fst) Dⱽ.Cᴰ

  reindexes a vertical displayed BiCCC `Dⱽ` along the PAIRED
  interpretation `pointwise = ⟨F,G⟩ : FREE → D × D` (`elimLocalMotive`)
  and feeds it to the free model's eliminator (`elimLocal`); the
  fundamental lemma is the resulting SECTION and is never written by
  hand.  `Bᴰ`/`reindexPair`/`indTm` are `Dⱽ`/`elimLocalMotive`/`elimLocal`.

  PHASE

  Phase 1 throughout, and deliberately: `indTm` is the ONE structural
  recursion on `Tm` this file contains, and it exists so that no phase-2
  file has to contain another.  Everything below `indTm` is data.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Elim where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt; Unit*; tt*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.LinLam.Opt public

private variable ℓ ℓ' : Level

-- §1 DISPLAYED GRAMMARS. A displayed grammar over `A` is exactly the
-- second argument of `Rules._&ᵈ_` -- the dependent additive conjunction --
-- so `A &ᵈ Aᴰ` is its total space and `&ᵈ-E₁` is the projection.

Ctxᴰ : Ctx → (ℓ : Level) → Type (ℓ-suc ℓ)
Ctxᴰ A ℓ = (u : Usage) → A u → Type ℓ

-- the total space, and a section: a displayed grammar is a `Ctx` over
-- `A` and a section of it is a proof "every element of `A` satisfies it"
Total : {A : Ctx} → Ctxᴰ A ℓ → TheoryTy ℓ tt
Total {A = A} Aᴰ = A &ᵈ Aᴰ

Sectionᴰ : {A : Ctx} → Ctxᴰ A ℓ → Type ℓ
Sectionᴰ {A = A} Aᴰ = (u : Usage) (x : A u) → Aᴰ u x

-- a DISPLAYED TERM over `f : A ⊢ B`
_⊢[_]_ : {A B : Ctx} → Ctxᴰ A ℓ → (A ⊢ B) → Ctxᴰ B ℓ' → Type (ℓ-max ℓ ℓ')
_⊢[_]_ {A = A} Aᴰ f Bᴰ = (u : Usage) (x : A u) → Aᴰ u x → Bᴰ u (f u x)

-- REINDEXING of a displayed grammar along a term.  (`pull` of
-- `Reindex.Base` moves the CARRIER; this moves the PAYLOAD, which is
-- the direction a logical relation travels.)
pullᴰ : {A B : Ctx} → (A ⊢ B) → Ctxᴰ B ℓ → Ctxᴰ A ℓ
pullᴰ f Bᴰ u x = Bᴰ u (f u x)

-- §1.1  THE DISPLAYED CONNECTIVES.  One per former of `StepG`.

oneᴰ : {A : Ctx} → Ctxᴰ A ℓ-zero
oneᴰ _ _ = Unit*

_⊕ᴰ'_ : {A B : Ctx} → Ctxᴰ A ℓ → Ctxᴰ B ℓ → Ctxᴰ (A ⊕ B) ℓ
(Aᴰ ⊕ᴰ' Bᴰ) u (inl x) = Aᴰ u x
(Aᴰ ⊕ᴰ' Bᴰ) u (inr y) = Bᴰ u y

-- the displayed tensor: a splitting is already shared, so all that is
-- displayed is the pair of payloads at the two slots.
_⊛ᴰ_ : {A B : Ctx} → Ctxᴰ A ℓ → Ctxᴰ B ℓ → Ctxᴰ (A ⊛ B) ℓ
(Aᴰ ⊛ᴰ Bᴰ) u (sp , k) = Aᴰ _ (k true) × Bᴰ _ (k false)

BodyOfᴰ : {A : Ctx} → Ctxᴰ A ℓ → Ctxᴰ (BodyOf A) ℓ
BodyOfᴰ Aᴰ u b = Aᴰ (true ∷ u) b

-- §2  THE SHAPE FUNCTOR, ITS ACTION, AND ITS DISPLAYED FORM.

-- `StepG` is a functor.  `Opt.agda` needed only its algebras, so this
-- was never written down; the reindexing theorem needs it.
StepG-map : {A B : Ctx} → (A ⊢ B) → StepG A ⊢ StepG B
StepG-map f u (inl s) = inl s
StepG-map f u (inr (inl (sp , k))) =
  inr (inl (⊛-mk _ _ u (sp .fst) (sp .snd .fst) (sp .snd .snd)
                   (f _ (k true)) (f _ (k false))))
StepG-map f u (inr (inr b)) = inr (inr (f (true ∷ u) b))

StepGᴰ : (A : Ctx) → Ctxᴰ A ℓ → Ctxᴰ (StepG A) ℓ
StepGᴰ A Aᴰ = oneᴰ' ⊕ᴰ' ((Aᴰ ⊛ᴰ Aᴰ) ⊕ᴰ' BodyOfᴰ Aᴰ)
  where
  -- `oneᴰ` at the ambient level, so the three summands agree
  oneᴰ' : Ctxᴰ SoloG _
  oneᴰ' _ _ = Unit*

-- A DISPLAYED ALGEBRA is a displayed term over the algebra.
Algᴰ : (A : Ctx) → (StepG A ⊢ A) → Ctxᴰ A ℓ → Type ℓ
Algᴰ A α Aᴰ = StepGᴰ A Aᴰ ⊢[ α ] Aᴰ

-- §3 THE ELIMINATOR. THE one structural recursion.

indTm : {Aᴰ : Ctxᴰ TmG ℓ} → Algᴰ TmG roll Aᴰ → Sectionᴰ Aᴰ
indTm αᴰ u (tvar s) = αᴰ u (inl s) tt*
indTm {Aᴰ = Aᴰ} αᴰ u (tapp {u₁} {u₂} s a b) =
  αᴰ u (inr (inl (⊛-mk TmG TmG u u₁ u₂ s a b)))
      (indTm {Aᴰ = Aᴰ} αᴰ u₁ a , indTm {Aᴰ = Aᴰ} αᴰ u₂ b)
indTm {Aᴰ = Aᴰ} αᴰ u (tlam b) =
  αᴰ u (inr (inr b)) (indTm {Aᴰ = Aᴰ} αᴰ (true ∷ u) b)

-- §4  `foldTm` IS `indTm` AT A CONSTANT MOTIVE, and the η-laws.
--
-- Mirrors `TheoryGrammar.Induction`'s `foldD`/`fold≡`/`indμ-unique`.

-- an algebra is a displayed algebra at a motive that ignores the term
constᴰ : Ctx → Ctxᴰ TmG ℓ-zero
constᴰ A u _ = A u

algᴰ : (A : Ctx) → (StepG A ⊢ A) → Algᴰ TmG roll (constᴰ A)
algᴰ A α u (inl s)              _       = α u (inl s)
algᴰ A α u (inr (inl (sp , k))) (p , q) =
  α u (inr (inl (⊛-mk A A u (sp .fst) (sp .snd .fst) (sp .snd .snd) p q)))
algᴰ A α u (inr (inr b))        p       = α u (inr (inr p))

foldD : (A : Ctx) → (StepG A ⊢ A) → TmG ⊢ A
foldD A α = indTm (algᴰ A α)

-- THE η-RULE the eliminator buys: two maps out of `TmG` agreeing on the
-- three rules agree everywhere.  `Opt.foldRoll` is the instance at
-- `g = foldTm TmG roll`, `h = idg`; nothing else in the tree had it.
indTm-unique : {Aᴰ : Ctxᴰ TmG ℓ} (g h : Sectionᴰ Aᴰ)
             → ((u : Usage) (x : StepG TmG u)
                → StepGᴰ TmG (λ v t → g v t ≡ h v t) u x
                → g u (roll u x) ≡ h u (roll u x))
             → (u : Usage) (t : Tm u) → g u t ≡ h u t
indTm-unique g h step = indTm step

-- ... and the initiality statement it is really for: `foldTm` is the
-- UNIQUE algebra map out of `TmG`.  `Opt.agda` proved only the instance
-- `foldTm TmG roll ≡ idPass`.
foldUnique : (A : Ctx) (α : StepG A ⊢ A) (h : TmG ⊢ A)
           → ((u : Usage) (x : StepG TmG u)
              → h u (roll u x) ≡ α u (StepG-map h u x))
           → (u : Usage) (t : Tm u) → h u t ≡ foldTm A α u t
foldUnique A α h isMap = indTm {Aᴰ = λ u t → h u t ≡ foldTm A α u t} step
  where
  step : Algᴰ TmG roll (λ u t → h u t ≡ foldTm A α u t)
  step u (inl s)              _       = isMap u (inl s)
  step u (inr (inl (sp , k))) (p , q) =
    isMap u (inr (inl (sp , k)))
    ∙ cong₂ (λ x y → α u (inr (inl (⊛-mk A A u (sp .fst) (sp .snd .fst)
                                        (sp .snd .snd) x y))))
            p q
  step u (inr (inr b))        p       =
    isMap u (inr (inr b)) ∙ cong (λ x → α u (inr (inr x))) p

-- ... so `foldD` and `foldTm` are the same function.
foldD≡ : (A : Ctx) (α : StepG A ⊢ A) (u : Usage) (t : Tm u)
       → foldD A α u t ≡ foldTm A α u t
foldD≡ A α = foldUnique A α (foldD A α) step
  where
  step : (u : Usage) (x : StepG TmG u)
       → foldD A α u (roll u x) ≡ α u (StepG-map (foldD A α) u x)
  step u (inl s)              = refl
  step u (inr (inl (sp , k))) = refl
  step u (inr (inr b))        = refl

-- `Opt.foldRoll`, re-derived with no induction of its own
foldRoll' : (u : Usage) (t : Tm u) → foldTm TmG roll u t ≡ t
foldRoll' u t = sym (foldUnique TmG roll idg step u t)
  where
  step : (u : Usage) (x : StepG TmG u) → roll u x ≡ roll u (StepG-map idg u x)
  step u (inl s)              = refl
  step u (inr (inl (sp , k))) = refl
  step u (inr (inr b))        = refl

-- §5 THE REINDEXING THEOREM. The paired interpretation `⟨ idg , foldTm B β
-- ⟩`, its algebra, and the transport of a displayed algebra along it.

module _ (B : Ctx) (β : StepG B ⊢ B) where

  -- the source paired with its image; the c-c-l `pointwise = ⟨F,G⟩`
  pairFold : TmG ⊢ (TmG & B)
  pairFold = &-I idg (foldTm B β)

  -- the algebra `pairFold` is a map into.  Componentwise: `roll` after
  -- forgetting the target, `β` after forgetting the source.
  pairAlg : StepG (TmG & B) ⊢ (TmG & B)
  pairAlg = &-I (roll ∘g StepG-map (λ _ → fst)) (β ∘g StepG-map (λ _ → snd))

  -- THE THEOREM. A displayed algebra over the paired target reindexes to
  -- one over the free model.
  reindexPair : (Bᴰ : Ctxᴰ (TmG & B) ℓ)
              → Algᴰ (TmG & B) pairAlg Bᴰ
              → Algᴰ TmG roll (pullᴰ pairFold Bᴰ)
  reindexPair Bᴰ βᴰ u (inl s)              xᴰ = βᴰ u (inl s) xᴰ
  reindexPair Bᴰ βᴰ u (inr (inl (sp , k))) xᴰ =
    βᴰ u (inr (inl (⊛-mk (TmG & B) (TmG & B) u (sp .fst) (sp .snd .fst)
                         (sp .snd .snd)
                         (pairFold _ (k true)) (pairFold _ (k false)))))
         xᴰ
  reindexPair Bᴰ βᴰ u (inr (inr b))        xᴰ =
    βᴰ u (inr (inr (pairFold (true ∷ u) b))) xᴰ

  -- THE FUNDAMENTAL LEMMA, for any displayed model over the target.
  -- No induction here and none at the call site: `indTm` is the whole
  -- recursion, `reindexPair` is the whole coercion.
  fundamental : (Bᴰ : Ctxᴰ (TmG & B) ℓ)
              → Algᴰ (TmG & B) pairAlg Bᴰ
              → (u : Usage) (t : Tm u) → Bᴰ u (t , foldTm B β u t)
  fundamental Bᴰ βᴰ = indTm (reindexPair Bᴰ βᴰ)
