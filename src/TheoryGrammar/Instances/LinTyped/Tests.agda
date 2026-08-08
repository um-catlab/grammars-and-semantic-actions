{- The pipeline computes. Each `refl` holds only if `typecheck`, the
   generic μ's `sup`/`fold`, `dec-⌈⌉ᵗ`, `dec-Look` AND `dec-SplitG` all
   reduce -- the last being the one this instance adds: an existential over
   the splittings of the context. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; snotz; injSuc)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Unit

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.View
open import TheoryGrammar.Instances.LinTyped
open Views linFib using (completeCase; certifies)

-- Types and terms.  De Bruijn: index 0 is the innermost binder, and
-- the head of a `Ctx` is the innermost slot.

o : Ty
o = base

oo : Ty
oo = o ⊸ᵗ o

-- LINEAR: every bound variable used exactly once
idAnn : Raw
idAnn = ann (lam (var 0)) (o ⊸ᵗ o)                    -- λx. x

idHi : Raw
idHi = ann (lam (var 0)) (oo ⊸ᵗ oo)                   -- λx. x  at (o⊸o)

selfApp : Raw
selfApp = app idHi idAnn                              -- gives o ⊸ o

compose : Raw                                          -- λf.λg.λx. f (g x)
compose = ann (lam (lam (lam (app (var 2) (app (var 1) (var 0))))))
              (oo ⊸ᵗ (oo ⊸ᵗ oo))

bare : Raw
bare = lam (var 0)                                    -- NOT annotated

-- NOT LINEAR, but simply typeable: `y` is discarded
kAnn : Raw
kAnn = ann (lam (lam (var 1))) (o ⊸ᵗ (o ⊸ᵗ o))       -- λx.λy. x

-- NOT LINEAR, but simply typeable: `x` is used twice
dupAnn : Raw
dupAnn = ann (lam (lam (app (app (var 1) (var 0)) (var 0))))
              ((o ⊸ᵗ (o ⊸ᵗ o)) ⊸ᵗ (o ⊸ᵗ o))         -- λf.λx. f x x

-- ill typed for the ordinary reasons
badArg : Raw
badArg = app idAnn idAnn                              -- o expected, o⊸o given

badAnn : Raw
badAnn = ann (lam (var 0)) o                          -- a lambda at a base type

freeVar : Raw
freeVar = var 0                                       -- unbound

-- The observations, all GENERIC (TheoryGrammar.SemanticAction), and all
-- TERMS: `run` / `runΔ` appear only in the `refl` lines.

infers! : ⊤G ⊢ Δ Bool
infers! = okA (Syn []) (¬G (Syn [])) ∘g closed-infer?

checks! : (C : Ty) → ⊤G ⊢ Δ Bool
checks! C = okA (Check [] C) (¬G (Check [] C)) ∘g closed-check? C

synth : ⊤G ⊢ Result (¬G (Syn [])) (Δ Ty)
synth = mapR (¬G (Syn [])) (Δ Ty) (tagA Ty) ∘g closed-infer?

-- LINEARITY, as the difference between two columns.

_ : passes (run infers! at ( idAnn   ↦ true
                           ∷ idHi    ↦ true
                           ∷ selfApp ↦ true
                           ∷ compose ↦ true
                           ∷ kAnn    ↦ false     -- discards `y`
                           ∷ dupAnn  ↦ false     -- uses `x` twice
                           ∷ bare    ↦ false     -- unannotated
                           ∷ badArg  ↦ false
                           ∷ badAnn  ↦ false
                           ∷ freeVar ↦ false
                           ∷ [] ))
_ = refl

-- the synthesised types are the expected ones
_ : passes (runΔ Ty (¬G (Syn [])) synth at
             ( idAnn   ↦ just (o ⊸ᵗ o)
             ∷ selfApp ↦ just (o ⊸ᵗ o)
             ∷ compose ↦ just (oo ⊸ᵗ (oo ⊸ᵗ oo))
             ∷ kAnn    ↦ nothing
             ∷ dupAnn  ↦ nothing
             ∷ bare    ↦ nothing
             ∷ [] ))
_ = refl

-- The MODE DISCIPLINE: a bare lambda synthesises nothing, but checks
-- at the right type and only at the right type.

_ : passes (run (checks! (o ⊸ᵗ o)) at ( bare    ↦ true
                                       ∷ selfApp ↦ true
                                       ∷ badArg  ↦ false
                                       ∷ [] ))
_ = refl

_ : passes (run (checks! o) at (bare ↦ false ∷ selfApp ↦ false ∷ []))
_ = refl

_ : passes (run (checks! (oo ⊸ᵗ o)) at (bare ↦ false ∷ []))
_ = refl

-- `dec-Look`: OWNING the context, not merely being bound in it.  This
-- is the variable rule's premise, and the second suite is the whole
-- difference from the cartesian `Lookup`.

bound? : (Γ : Ctx) → ⊤G ⊢ Δ Bool
bound? Γ = okA (Look Γ) (¬G (Look Γ)) ∘g dec-Look Γ

typeOf : (Γ : Ctx) → ⊤G ⊢ Result (¬G (Look Γ)) (Δ Ty)
typeOf Γ = mapR (¬G (Look Γ)) (Δ Ty) (tagA Ty) ∘g dec-Look Γ

Γ₁ : Ctx
Γ₁ = just oo ∷ just o ∷ []          -- index 0 : o ⊸ o,  index 1 : o

_ : passes (runΔ Ty _ (typeOf (just o ∷ [])) at (0 ↦ just o ∷ 1 ↦ nothing ∷ []))
_ = refl

_ : passes (runΔ Ty _ (typeOf (nothing ∷ just oo ∷ [])) at
             (0 ↦ nothing ∷ 1 ↦ just oo ∷ []))
_ = refl

-- TWO live slots: NEITHER index owns the context outright
_ : passes (run (bound? Γ₁) at (0 ↦ false ∷ 1 ↦ false ∷ []))
_ = refl

_ : passes (run (bound? []) at (0 ↦ false ∷ []))
_ = refl

-- ... and hence the same at the level of the judgment: a term must use
-- EVERY slot its context owns.

inferIn : (Γ : Ctx) → ⊤G ⊢ Result (¬G (Syn Γ)) (Δ Ty)
inferIn Γ = mapR (¬G (Syn Γ)) (Δ Ty) (tagA Ty) ∘g (&ᴰ-E Ctx Γ ∘g infer?)

checkIn : (Γ : Ctx) (C : Ty) → ⊤G ⊢ Δ Bool
checkIn Γ C = okA (Check Γ C) (¬G (Check Γ C))
              ∘g (&ᴰ-E (Ctx × Ty) (Γ , C) ∘g check?)

-- `app (var 0) (var 1)` splits Γ₁ as [o⊸o, -] ⊎ [-, o]; nothing else
-- typechecks, and `var 0` alone leaves slot 1 unused.
_ : passes (runΔ Ty _ (inferIn Γ₁) at
             ( (app (var 0) (var 1)) ↦ just o
             ∷ (app (var 0) (var 0)) ↦ nothing     -- slot 0 twice, slot 1 never
             ∷ (var 0)               ↦ nothing     -- slot 1 unused
             ∷ (var 1)               ↦ nothing     -- slot 0 unused
             ∷ [] ))
_ = refl

_ : passes (runΔ Ty _ (inferIn (just o ∷ [])) at
             ((var 0) ↦ just o ∷ (var 1) ↦ nothing ∷ []))
_ = refl

_ : passes (run (checkIn (just o ∷ []) o) at ((var 0) ↦ true ∷ []))
_ = refl

_ : passes (run (checkIn (just o ∷ []) oo) at ((var 0) ↦ false ∷ []))
_ = refl

-- The other maps out of `⊤` in this instance, at all three SORTS.

-- ---- `dec-⌈⌉ᵗ` : the representable at a TYPE (world = Ty)
isTy? : (A : Ty) → ⊤G ⊢ Δ Bool
isTy? A = okA (⌈_⌉ {s = ty} A) (¬G (⌈_⌉ {s = ty} A)) ∘g dec-⌈⌉ᵗ A

_ : passes (run (isTy? o) at (o ↦ true ∷ oo ↦ false ∷ []))
_ = refl

_ : passes (run (isTy? oo) at (oo ↦ true ∷ o ↦ false ∷ []))
_ = refl

_ : passes (run (isTy? (o ⊸ᵗ oo)) at
             ((oo ⊸ᵗ o) ↦ false ∷ (o ⊸ᵗ oo) ↦ true ∷ []))
_ = refl

-- ---- `dec-⌈⌉ⁿ` : the representable at an INDEX (world = ℕ)
isIx? : (m : ℕ) → ⊤G ⊢ Δ Bool
isIx? m = okA (Nm m) (¬G (Nm m)) ∘g dec-⌈⌉ⁿ m

_ : passes (run (isIx? 2) at (2 ↦ true ∷ 5 ↦ false ∷ []))
_ = refl

-- ---- `⊗-decSplit` : "is this term built by this operation?"
isOp! : (op : TOp) → ⊤G ⊢ Δ Bool
isOp! op = okA (⊗ˢ op (λ _ → ⊤G)) (¬G (⊗ˢ op (λ _ → ⊤G))) ∘g ⊗-decSplit op

_ : passes (run (isOp! varOp) at ((var 0) ↦ true ∷ idAnn ↦ false ∷ []))
_ = refl

_ : passes (run (isOp! lamOp) at ((var 0) ↦ false ∷ bare ↦ true ∷ []))
_ = refl

_ : passes (run (isOp! annOp) at (idAnn ↦ true ∷ []))
_ = refl

_ : passes (run (isOp! appOp) at (selfApp ↦ true ∷ []))
_ = refl

-- ... and at the `ty` sort, where the world is a TYPE, not a term
_ : passes (run (isOp! lolOp)  at (oo ↦ true ∷ o ↦ false ∷ []))
_ = refl

_ : passes (run (isOp! baseOp) at (o ↦ true ∷ []))
_ = refl

-- THE REJECTIONS, AS THEOREMS. `refute` turns each negative observation
-- into the refutation the decision was carrying: `Syn [] t → ⊥` says the
-- term has NO linear type in the empty context.

noSyn : (t : Raw) → run infers! t ≡ false → (¬G (Syn [])) t
noSyn = refute (Syn []) (¬G (Syn [])) closed-infer?

noChk : (C : Ty) (t : Raw) → run (checks! C) t ≡ false → (¬G (Check [] C)) t
noChk C = refute (Check [] C) (¬G (Check [] C)) (closed-check? C)

-- LINEARITY, AS A THEOREM.  Both of these are simply typeable; neither
-- has ANY linear type, and the refutation is the content.
no-syn-kAnn : (¬G (Syn [])) kAnn            -- λx.λy. x  discards `y`
no-syn-kAnn = noSyn kAnn refl

no-syn-dupAnn : (¬G (Syn [])) dupAnn        -- λf.λx. f x x  uses `x` twice
no-syn-dupAnn = noSyn dupAnn refl

-- ... and at the checking side, where the type is supplied
no-chk-k : (¬G (Check [] (o ⊸ᵗ (o ⊸ᵗ o)))) (lam (lam (var 1)))
no-chk-k = noChk (o ⊸ᵗ (o ⊸ᵗ o)) (lam (lam (var 1))) refl

-- ill typed for the ordinary reasons, also as theorems
no-syn-bare : (¬G (Syn [])) bare
no-syn-bare = noSyn bare refl

no-syn-badArg : (¬G (Syn [])) badArg
no-syn-badArg = noSyn badArg refl

no-syn-badAnn : (¬G (Syn [])) badAnn
no-syn-badAnn = noSyn badAnn refl

no-syn-freeVar : (¬G (Syn [])) freeVar
no-syn-freeVar = noSyn freeVar refl

no-chk-bare-o : (¬G (Check [] o)) bare
no-chk-bare-o = noChk o bare refl

-- ... and the well-typed side is a WITNESS, not a report
yes-syn-idAnn : Syn [] idAnn
yes-syn-idAnn = witness (Syn []) (¬G (Syn [])) closed-infer? idAnn refl

yes-syn-compose : Syn [] compose
yes-syn-compose = witness (Syn []) (¬G (Syn [])) closed-infer? compose refl

yes-chk-bare : Check [] (o ⊸ᵗ o) bare
yes-chk-bare = witness (Check [] (o ⊸ᵗ o)) (¬G (Check [] (o ⊸ᵗ o)))
                       (closed-check? (o ⊸ᵗ o)) bare refl

-- THE PARTITIONS, one per sort (LinTyped.Readable).

tmName : ⊤G ⊢ Δ ℕ
tmName = completeCase tmCase λ { oVar → pureA ℕ 0 ; oApp → pureA ℕ 1
                               ; oLam → pureA ℕ 2 ; oAnn → pureA ℕ 3 }

tyName : ⊤G ⊢ Δ ℕ
tyName = completeCase tyCase λ { oBase → pureA ℕ 0 ; oLol → pureA ℕ 1 }

_ : passes (run tmName at
             ( (var 0) ↦ 0 ∷ selfApp ↦ 1 ∷ bare ↦ 2 ∷ idAnn ↦ 3 ∷ [] ))
_ = refl

_ : passes (run tyName at (o ↦ 0 ∷ oo ↦ 1 ∷ []))
_ = refl

-- the certificate: an annotation is not a lambda, positively
ann-not-lam : tmB oAnn ⊢ ¬G (tmB oLam)
ann-not-lam = certifies tmCase oAnn oLam λ p → snotz (injSuc (injSuc (cong tag p)))
  where tag : TmOp → ℕ
        tag oVar = 0
        tag oApp = 1
        tag oLam = 2
        tag oAnn = 3

-- a lollipop type is not a base type
lol-not-base : tyB oLol ⊢ ¬G (tyB oBase)
lol-not-base = certifies tyCase oLol oBase λ p → snotz (cong tag p)
  where tag : TyOp → ℕ
        tag oBase = 0
        tag oLol  = 1
