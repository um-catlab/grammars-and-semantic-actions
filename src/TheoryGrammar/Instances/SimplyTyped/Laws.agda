{-
  MEASUREMENT: which laws of this instance hold by `refl`, and which
  need `funExt`.

  The pattern is uniform and has one cause, the one named in
  `TheoryGrammar.Fibered`:

    * `Σ`, `Π`, `Unit`, `Unit*` and `Lift` have definitional η, so any
      round trip that only reassociates or re-wraps is `refl`;
    * `Bool` (an arity) and `Eq._≡_` (a proof carried in a slot) do NOT,
      so any round trip that REBUILDS a function over an arity, or that
      has to look at a representable's proof, needs `funExt` -- with
      `refl` at every leaf.

  So the funExt debt of the whole instance is exactly "one per Bool
  arity" plus "one per Eq match", and nothing else.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.List using (_∷_)
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.SimplyTyped

module StLaws (Name : Type₀) (_≟_ : Discrete Name) where

  open SimplyTyped Name _≟_

  -- ================================================================
  -- REFL.  The multiplicative universal property, at every operation
  -- including the empty one.  Inherited from the promodel: `Split` is
  -- data, so there is no proof term to match.
  -- ================================================================

  ⊗-βη : (o : TOp)
         {A : (a : TAr o) → TheoryTy ℓ-zero (TSortOf o a)}
         {B : TheoryTy ℓ-zero (TResult o)}
       → ((g : MultiHomˢ o A B)
          → curryˢ o {A = A} {B = B} (uncurryˢ o {A = A} {B = B} g) ≡ g)
       × ((f : ⊗ˢ o A ⊢ B)
          → uncurryˢ o {A = A} {B = B} (curryˢ o {A = A} {B = B} f) ≡ f)
  ⊗-βη o = (λ _ → refl) , (λ _ → refl)

  -- ================================================================
  -- REFL.  The unary tensor's index can be pushed in and pulled out
  -- freely: `Unit`'s η makes the slot function trivial and `Σ`'s η
  -- makes the pair trivial.  This is the whole reason `varG-pull` is
  -- harmless even though it is not internal.
  -- ================================================================

  varG-rt : (Γ : Ctx) → (varG-push Γ ∘g varG-pull Γ) ≡ idg {A = VarG (Look Γ)}
  varG-rt Γ = refl

  varG-rt⁻ : (Γ : Ctx)
           → (varG-pull Γ ∘g varG-push Γ) ≡ idg {A = ⊕ᴰ Ty (QVar Γ)}
  varG-rt⁻ Γ = refl

  -- ================================================================
  -- REFL one way, funExt the other.  `app-collapse` only reassociates,
  -- so rebuilding the PAIR is free; rebuilding the Bool-indexed SLOT
  -- FUNCTION is not.
  -- ================================================================

  app-rt : (Γ : Ctx)
         → (app-collapse Γ ∘g app-collapse⁻ Γ) ≡ idg {A = AppGᵈ Γ}
  app-rt Γ = refl

  app-rt⁻ : (Γ : Ctx)
          → (app-collapse⁻ Γ ∘g app-collapse Γ) ≡ idg {A = SynApp Γ}
  app-rt⁻ Γ = funExt λ t → funExt λ
    { (AB , sp , h) →
        cong (λ z → AB , sp , z) (funExt λ { true → refl ; false → refl }) }

  -- ================================================================
  -- The container/connective respelling.  `chk`'s switch rule is REFL
  -- -- its position type is `Unit*`, which has η -- and every other
  -- clause needs exactly one `funExt`, over a `Bool` arity or over an
  -- empty position type, with `refl` inside.
  -- ================================================================

  -- The `var` alternative is REFL: its shape is rebuilt by `lift ∘
  -- lower` (η) and its position type is empty, so nothing has to be
  -- reassembled.  `switch` is REFL for the same reason one level up --
  -- its position type is `Unit*`.  The three alternatives whose
  -- operation has a `Bool` arity each cost exactly one `funExt`.
  ⟦J⟧-rt⁻ : {M : Ix → Type₀} (x : NT) → (⟦J⟧ {M} x ∘g ⟦J⟧⁻ {M} x) ≡ idg
  ⟦J⟧-rt⁻ {M} (syn , Γ , A) = funExt λ t → funExt λ
    { (inl (sp , h))            → refl
    ; (inr (inl (A₀ , sp , h))) →
        cong (wrapApp A₀ sp) (funExt λ { true → refl ; false → refl })
    ; (inr (inr (sp , h)))      →
        cong (wrapAnn sp) (funExt λ { true → refl ; false → refl })
    }
    where
    R : NT → TmG
    R y s = M (y , s)

    wrapApp : {t : Raw} (A₀ : Ty) (sp : IsApp t)
            → ((b : Bool) → appFam (R (syn , Γ , A₀ ⇒ᵗ A)) (R (chk , Γ , A₀)) b
                                   (TParts appOp t sp b))
            → JStep R (syn , Γ , A) t
    wrapApp A₀ sp z = inr (inl (A₀ , sp , z))

    wrapAnn : {t : Raw} (sp : IsAnn t)
            → ((b : Bool) → annFam (R (chk , Γ , A)) (⌈_⌉ {s = ty} A) b
                                   (TParts annOp t sp b))
            → JStep R (syn , Γ , A) t
    wrapAnn sp z = inr (inr (sp , z))
  ⟦J⟧-rt⁻ {M} (chk , Γ , C) = funExt λ t → funExt λ
    { (inl d) → refl
    ; (inr (sa , n , sp , h)) →
        cong (wrapLam sa n sp) (funExt λ { true → refl ; false → refl })
    }
    where
    R : NT → TmG
    R y s = M (y , s)

    wrapLam : {t : Raw} (sa : IsArr C) (n : Name) (sp : IsLam t)
            → ((b : Bool) → lamFam (Nm n) (R (chk , (n , dom sa) ∷ Γ , cod sa)) b
                                   (TParts lamOp t sp b))
            → JStep R (chk , Γ , C) t
    wrapLam sa n sp z = inr (sa , n , sp , z)

  -- ... and hence the judgments' own unroll/roll, since `μ-coalg` after
  -- `μ-alg` is the identity by `refl` (the fixed point is a container,
  -- so its algebra is a pair, and pairs have η).
  j-rt⁻ : (x : NT) → (j-unroll x ∘g j-roll x) ≡ idg {A = JStep Jμ x}
  j-rt⁻ x = ⟦J⟧-rt⁻ x

  -- NOT STATED: the other composite `⟦J⟧⁻ ∘ ⟦J⟧ ≡ idg` is true but its
  -- statement is a `PathP`, not a `Path`: in the container form the
  -- position function's TYPE depends on the shape, and the shape is the
  -- component that needs the `funExt`.  That is a cost of the container
  -- presentation, not of the theory -- the connective form `⟦_⟧c` has
  -- no such dependency.
