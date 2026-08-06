{-
  The pipeline computes.  Each `refl` holds only if `typecheck`, the
  generic μ's `sup`/`fold`, `dec-⌈⌉ᵗ` (which is `dec-⊗` at the `ty`
  sort) and `dec-Look` all reduce.

  Every name below is a TERM of the calculus -- `⊤G ⊢ Δ Bool` or
  `⊤G ⊢ Result (¬G _) (Δ Ty)` -- and `run` / `runΔ` appear only in the
  `refl` lines.  Cases are batched into suites with `passes … at …`.
  This file defines no reader and no constant grammar.

  The mode discipline shows up as a pair of tests on the SAME term:
  `lam 0 (var 0)` does not synthesise, and does check at `base ⇒ base`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe using (Maybe; just; nothing)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.SimplyTyped
open SimplyTyped ℕ discreteℕ

-- ==================================================================
-- Terms.  With no constants at `base`, every closed term is built from
-- annotated lambdas -- which is exactly the point of `ann`.
-- ==================================================================

o : Ty
o = base

idAnn                                     : Raw
idAnn = ann (lam 0 (var 0)) (o ⇒ᵗ o)                  -- (λx. x) : o → o

idHi : Raw
idHi = ann (lam 0 (var 0)) ((o ⇒ᵗ o) ⇒ᵗ (o ⇒ᵗ o))     -- (λx. x) : (o→o)→(o→o)

kAnn : Raw
kAnn = ann (lam 0 (lam 1 (var 0))) (o ⇒ᵗ (o ⇒ᵗ o))    -- K : o → o → o

selfApp : Raw
selfApp = app idHi idAnn                              -- well typed, gives o → o

bare : Raw
bare = lam 0 (var 0)                                  -- NOT annotated

badArg : Raw
badArg = app idAnn idAnn                              -- o expected, o→o given

badAnn : Raw
badAnn = ann (lam 0 (var 0)) o                        -- a lambda at a base type

freeVar : Raw
freeVar = var 0                                       -- unbound

shadow : Raw
shadow = ann (lam 0 (lam 0 (var 0))) (o ⇒ᵗ (o ⇒ᵗ o))  -- λx. λx. x

-- ==================================================================
-- The observations, all GENERIC (TheoryGrammar.SemanticAction), and all
-- TERMS: `⊤G ⊢ Δ Bool` and `⊤G ⊢ Result (¬G _) (Δ Ty)`.  `run` / `runΔ`
-- appear only in the `refl` lines -- externalising is the observation,
-- not part of the pipeline.
--
-- `closed-infer?` / `closed-check?` are decisions, i.e. maps out of `⊤`
-- at the shape `Result (¬G _) _`, so `okA` observes them.  The
-- SYNTHESISED TYPE is the witness, carried by `mapR` along the action
-- `tagA Ty` -- because `Syn Γ` IS a `⊕ᴰ Ty`, so its index is exactly
-- what the generic `tagA` projects.
--
-- Cases are batched with `passes (t at (w ↦ v ∷ …))`, so the term under
-- test is written once and one `refl` discharges the whole suite.
-- ==================================================================

infers! : ⊤G ⊢ Δ Bool
infers! = okA (Syn []) (¬G (Syn [])) ∘g closed-infer?

checks! : (C : Ty) → ⊤G ⊢ Δ Bool
checks! C = okA (Check [] C) (¬G (Check [] C)) ∘g closed-check? C

synth : ⊤G ⊢ Result (¬G (Syn [])) (Δ Ty)
synth = mapR (¬G (Syn [])) (Δ Ty) (tagA Ty) ∘g closed-infer?

-- ==================================================================
-- Synthesis, and the MODE DISCIPLINE: a bare lambda synthesises
-- nothing, but checks at the right type and only at the right type.
-- ==================================================================

_ : passes (run infers! at ( idAnn   ↦ true
                           ∷ kAnn    ↦ true
                           ∷ selfApp ↦ true
                           ∷ shadow  ↦ true
                           ∷ bare    ↦ false
                           ∷ badArg  ↦ false
                           ∷ badAnn  ↦ false
                           ∷ freeVar ↦ false
                           ∷ [] ))
_ = refl

_ : passes (run (checks! (o ⇒ᵗ o)) at ( bare    ↦ true
                                      ∷ selfApp ↦ true
                                      ∷ badArg  ↦ false
                                      ∷ [] ))
_ = refl

-- the switch rule really does compare types
_ : passes (run (checks! o) at (bare ↦ false ∷ selfApp ↦ false ∷ []))
_ = refl

_ : passes (run (checks! ((o ⇒ᵗ o) ⇒ᵗ o)) at (bare ↦ false ∷ []))
_ = refl

-- ==================================================================
-- The synthesised types are the expected ones.
-- ==================================================================

_ : passes (runΔ Ty (¬G (Syn [])) synth at
             ( idAnn   ↦ just (o ⇒ᵗ o)
             ∷ kAnn    ↦ just (o ⇒ᵗ (o ⇒ᵗ o))
             ∷ selfApp ↦ just (o ⇒ᵗ o)
             ∷ bare    ↦ nothing
             ∷ badArg  ↦ nothing
             ∷ [] ))
_ = refl

-- ==================================================================
-- EVERY OTHER MAP OUT OF `⊤` IN THIS INSTANCE.  These live at three
-- different SORTS -- names, types and terms -- and the interface does
-- not notice: the sort is just the world the term is run at.
-- ==================================================================

-- ---- `dec-⌈⌉ⁿ` : the representable at a NAME (world = Name)
isName? : (m : ℕ) → ⊤G ⊢ Δ Bool
isName? m = okA (Nm m) (¬G (Nm m)) ∘g dec-⌈⌉ⁿ m

_ : passes (run (isName? 2) at (2 ↦ true ∷ 5 ↦ false ∷ []))
_ = refl

-- ---- `dec-⌈⌉ᵗ` : the representable at a TYPE (world = Ty).  Deciding
-- ---- type equality is the `⊗ˢ` decision at the `ty` sort, recursively.
isTy? : (A : Ty) → ⊤G ⊢ Δ Bool
isTy? A = okA (⌈_⌉ {s = ty} A) (¬G (⌈_⌉ {s = ty} A)) ∘g dec-⌈⌉ᵗ A

_ : passes (run (isTy? o) at (o ↦ true ∷ (o ⇒ᵗ o) ↦ false ∷ []))
_ = refl

_ : passes (run (isTy? (o ⇒ᵗ o)) at ((o ⇒ᵗ o) ↦ true ∷ o ↦ false ∷ []))
_ = refl

_ : passes (run (isTy? (o ⇒ᵗ (o ⇒ᵗ o))) at
             (((o ⇒ᵗ o) ⇒ᵗ o) ↦ false ∷ (o ⇒ᵗ (o ⇒ᵗ o)) ↦ true ∷ []))
_ = refl

-- ---- `dec-Look` : context lookup.  `Look Γ = ⊕ᴰ Ty (Lookup Γ)`, so
-- ---- the WITNESS is the type found, and carrying it is `mapR` along
-- ---- `tagA Ty` -- the same action `synth` uses.
bound? : (Γ : Ctx) → ⊤G ⊢ Δ Bool
bound? Γ = okA (Look Γ) (¬G (Look Γ)) ∘g dec-Look Γ

typeOf : (Γ : Ctx) → ⊤G ⊢ Result (¬G (Look Γ)) (Δ Ty)
typeOf Γ = mapR (¬G (Look Γ)) (Δ Ty) (tagA Ty) ∘g dec-Look Γ

Γ₀ : Ctx
Γ₀ = (0 , o) ∷ (1 , o ⇒ᵗ o) ∷ []

_ : passes (run (bound? []) at (0 ↦ false ∷ []))
_ = refl

_ : passes (run (bound? Γ₀) at (1 ↦ true ∷ 2 ↦ false ∷ []))
_ = refl

_ : passes (runΔ Ty _ (typeOf Γ₀) at
             (0 ↦ just o ∷ 1 ↦ just (o ⇒ᵗ o) ∷ 2 ↦ nothing ∷ []))
_ = refl

-- shadowing: the innermost binding wins
_ : passes (runΔ Ty _ (typeOf ((0 , o ⇒ᵗ o) ∷ (0 , o) ∷ [])) at
             (0 ↦ just (o ⇒ᵗ o) ∷ []))
_ = refl

-- ---- `infer?` / `check?` at a NON-EMPTY context.  `closed-infer?` is
-- ---- these at `[]`; `&ᴰ-E` is the generic way in, and after it the
-- ---- observation is unchanged.
inferIn : (Γ : Ctx) → ⊤G ⊢ Result (¬G (Syn Γ)) (Δ Ty)
inferIn Γ = mapR (¬G (Syn Γ)) (Δ Ty) (tagA Ty) ∘g (&ᴰ-E Ctx Γ ∘g infer?)

checkIn : (Γ : Ctx) (C : Ty) → ⊤G ⊢ Δ Bool
checkIn Γ C = okA (Check Γ C) (¬G (Check Γ C))
              ∘g (&ᴰ-E (Ctx × Ty) (Γ , C) ∘g check?)

-- a free variable synthesises nothing at `[]` and its type in `Γ₀`
_ : passes (runΔ Ty _ (inferIn []) at ((var 1) ↦ nothing ∷ []))
_ = refl

-- ... and the argument's type really is checked
_ : passes (runΔ Ty _ (inferIn Γ₀) at
             ( (var 1)              ↦ just (o ⇒ᵗ o)
             ∷ (app (var 1) (var 0)) ↦ just o
             ∷ (app (var 1) (var 1)) ↦ nothing
             ∷ [] ))
_ = refl

_ : passes (run (checkIn Γ₀ o) at ((var 0) ↦ true ∷ []))
_ = refl

-- a bare lambda checks under a context too
_ : passes (run (checkIn Γ₀ (o ⇒ᵗ o)) at ((var 0) ↦ false ∷ bare ↦ true ∷ []))
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
_ : passes (run (isOp! arrOp)  at ((o ⇒ᵗ o) ↦ true ∷ o ↦ false ∷ []))
_ = refl

_ : passes (run (isOp! baseOp) at (o ↦ true ∷ []))
_ = refl

-- ==================================================================
-- THE REJECTIONS, AS THEOREMS.
--
-- `refute` turns each negative observation into the refutation the
-- decision was carrying: `Syn [] t → ⊥` says the term has NO type in
-- the empty context, which is what "ill typed" is supposed to mean.  A
-- `≡ false` on its own only says the checker returned no.
-- ==================================================================

noSyn : (t : Raw) → run infers! t ≡ false → (¬G (Syn [])) t
noSyn = refute (Syn []) (¬G (Syn [])) closed-infer?

noChk : (C : Ty) (t : Raw) → run (checks! C) t ≡ false → (¬G (Check [] C)) t
noChk C = refute (Check [] C) (¬G (Check [] C)) (closed-check? C)

-- MODE DISCIPLINE, as a theorem in both directions: a bare lambda has
-- no synthesised type at all ...
no-syn-bare : (¬G (Syn [])) bare
no-syn-bare = noSyn bare refl

-- ... but it does CHECK at the right type, and at no other
yes-chk-bare : Check [] (o ⇒ᵗ o) bare
yes-chk-bare = witness (Check [] (o ⇒ᵗ o)) (¬G (Check [] (o ⇒ᵗ o)))
                       (closed-check? (o ⇒ᵗ o)) bare refl

no-chk-bare-o : (¬G (Check [] o)) bare
no-chk-bare-o = noChk o bare refl

no-chk-bare-hi : (¬G (Check [] ((o ⇒ᵗ o) ⇒ᵗ o))) bare
no-chk-bare-hi = noChk ((o ⇒ᵗ o) ⇒ᵗ o) bare refl

-- ILL TYPED, genuinely: no type exists, rather than none was found
no-syn-badArg : (¬G (Syn [])) badArg      -- o expected, o→o given
no-syn-badArg = noSyn badArg refl

no-syn-badAnn : (¬G (Syn [])) badAnn      -- a lambda at a base type
no-syn-badAnn = noSyn badAnn refl

no-syn-freeVar : (¬G (Syn [])) freeVar    -- unbound
no-syn-freeVar = noSyn freeVar refl

-- the switch rule really does compare types, and the mismatch is refuted
no-chk-selfApp : (¬G (Check [] o)) selfApp
no-chk-selfApp = noChk o selfApp refl

-- ... and the well-typed side is a witness, not a report
yes-syn-idAnn : Syn [] idAnn
yes-syn-idAnn = witness (Syn []) (¬G (Syn [])) closed-infer? idAnn refl
