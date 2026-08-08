{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PASS 1.  NAMED → DE BRUIJN, AS A REINDEXING.

  `CarrierMap.Reindex` is a map of `Fibered` over one signature whose
  source and target may DIFFER.  That is exactly what an elaboration is,
  and it is the only reason this pass can stay inside the calculus at
  all: `Lambda/Passes/Inline`'s `CarrierMap` is the endo case
  (`Fib' = Fib`), and no endo-map of `λFib` can be de Bruijn conversion,
  because the codomain is a different theory.

      hom nm  =  ρ₀              : Name → Σ[n] Fin n
      hom tm  =  toDB ρ₀         : Raw  → Σ[n] DBTm n

  and the two are the two components of one map of `λSig`-`Fibered`.

  WHY THE ELABORATION IS TOTAL, and why that is not a cheat.

  `Lambda/DeBruijn.toDB` is a fold over `Scoped Γ` -- it needs the input
  to be well-scoped before it can run.  Here `toDB` takes an
  ENVIRONMENT `ρ : Name → Fin j` and is total on `Raw`:

      toDB ρ (var n)   = dvar (ρ n)
      toDB ρ (app u v) = dapp (toDB ρ u) (toDB ρ v)
      toDB ρ (lam n t) = dlam (toDB (ext n ρ) t)

  Nothing is lost: a free name is elaborated to the index `ρ₀` assigns
  it, which is precisely what an ambient scope IS.  Totality is what
  makes `hom` a function on the whole carrier, hence a `Reindex`; a
  partial elaboration would be a map into `MaybeG` and not a reindexing
  at all.  This is the same move `Instances/Heap` makes with `_#_`: the
  side condition goes into the structure rather than into a `Maybe`.

  THE ADDITIVE FRAGMENT IS FREE, and what that actually buys.

  `Along.pull` reindexes a grammar over the TARGET to one over the
  source, and `pullTerm` reindexes every derivation, with NO hypothesis
  on `hom` -- `pull-⊤`, `pull-&`, `pull-⊕`, `pull-⇒`, `pull-⊕ᴰ`,
  `pull-&ᴰ`, `pull-⊥` are all `refl`.  The consequence demonstrated
  below is not decoration:

      elabScoped : ⊤G ⊢ S.pull DBAll

  says EVERY raw term elaborates to a well-scoped de Bruijn term, and
  its proof is `S.pullTerm dbAll` -- a theorem about the TARGET,
  transported.  No induction over `Raw` appears, and in particular the
  scope-checker of `Lambda/Passes/Decide` is not needed to state it: the
  reason the output is scoped has nothing to do with the input.

  Likewise `pull-Dec` is `refl`, so every internal decision over de
  Bruijn terms is automatically an internal decision about the
  elaboration of a named term -- `linear?` at the end of the file is
  that, at `Check.linear?`.

  THE MULTIPLICATIVE FRAGMENT, AND WHERE IT BREAKS.  This is the point
  of the file.  Of the three operations,

      varOp   PRESERVED   toDB ρ (var n)   = dvar (ρ n)
      appOp   PRESERVED   toDB ρ (app u v) = dapp (toDB ρ u) (toDB ρ v)
      lamOp   FAILS       toDB ρ (lam n t) = dlam (toDB (ext n ρ) t)

  and the failure is localised at exactly the operation the pass
  rewrites -- the same shape as `Passes/Inline`, where substitution
  preserves `appOp`/`lamOp` and fails at `varOp`.  Which operation is
  the obstruction is a property of the pass, and naming it is the
  content: for INLINING it is the variable, because that is the thing
  substitution replaces; for DE BRUIJN CONVERSION it is the binder,
  because that is the thing the reindexing consumes.

  The failure at `lamOp` is over-determined, and both halves are worth
  reading, because each of them is one half of what "de Bruijn" means:

    (i)  the NAME slot.  `parts lamOp` sends the source binder to `n`
         and the target binder to `fzero`.  `SplitPresAt` demands these
         agree under `hom`, i.e. `ρ n Eq.≡ fzero`, which holds for at
         most one name.  This is α-conversion refusing to be a
         homomorphism.

    (ii) the SCOPE.  The body slot moves from scope `j` to scope
         `suc j`, so the two sides of `homParts` do not even live over
         the same point of `carrier tm`.  This is the reindexing
         (`ext n ρ`) refusing to be constant.

  `¬presLam` below is proved from (ii), because that half is
  refutable with no hypothesis on `Name` at all.

  REFLECTION, by contrast, is POSITIVE at `varOp` and `appOp`
  (`reflVar`, `reflApp`): `toDB` maps constructors to constructors, so
  a de Bruijn application can only have come from a named application.
  Compare `Inline.¬subReflects`, which fails at `appOp` -- substitution
  can turn a variable into an application, elaboration can not turn one
  head symbol into another.  So the two passes fail in genuinely
  different places, and `CarrierMap`'s per-operation conditions are what
  makes the difference statable.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Scope where

open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.FinData.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Cubical.Relation.Nullary.Base using (Discrete; decRec)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Base

import TheoryGrammar.Instances.LinLam.DB    as D
import TheoryGrammar.Instances.LinLam.Check as C

-- The elaboration.  `k` and `ρ₀` are the AMBIENT SCOPE: which index a
-- free name denotes.  Nothing below depends on either being canonical.

module Elab (Name : Type₀) (_≟_ : Discrete Name)
            (k : ℕ) (ρ₀ : Name → Fin k) where

  open LamBase Name

  -- PRIMITIVE (phase 1): extending an environment under a binder.  The
  -- metalanguage `Dec` is consumed by its OWN eliminator `decRec`,
  -- exactly as `Inline.sub` does -- no `with`, no `yes`/`no` pattern.
  ext : {j : ℕ} → Name → (Name → Fin j) → (Name → Fin (suc j))
  ext n ρ m = decRec (λ _ → fzero) (λ _ → fsuc (ρ m)) (m ≟ n)

  -- PRIMITIVE (phase 1): the elaboration itself, TOTAL on `Raw`.
  toDB : {j : ℕ} → (Name → Fin j) → Raw → D.DBTm j
  toDB ρ (var n)   = D.dvar (ρ n)
  toDB ρ (app u v) = D.dapp (toDB ρ u) (toDB ρ v)
  toDB ρ (lam n t) = D.dlam (toDB (ext n ρ) t)

  -- THE REINDEXING.  Two sorts, two components, no laws.

  dbCM : Reindex λFib D.dbFib
  dbCM .hom nm n = k , ρ₀ n
  dbCM .hom tm t = k , toDB ρ₀ t

  private module S = Along dbCM

  -- POSITIVE, ADDITIVELY: no hypothesis at all, and nothing to prove.

  -- decidability transports definitionally ...
  pull-Dec : (A : D.TmG) → S.pull D.Dec⟨ A ⟩ ≡ Dec⟨ S.pull A ⟩
  pull-Dec A = refl

  -- ... and so does every other additive former
  pull-top : S.pull (D.⊤G {s = tm}) ≡ ⊤G
  pull-top = refl

  pull-and : (A B : D.TmG) → S.pull (A D.& B) ≡ (S.pull A & S.pull B)
  pull-and A B = refl

  -- THE DEMONSTRATION. `dbAll : ⊤G ⊢ DBAll` is a theorem about de Bruijn
  -- terms (`DB.agda`); `pullTerm` makes it a theorem about the ELABORATION
  -- of an arbitrary raw term, with no induction over `Raw` and no scope-
  -- checking hypothesis.
  elabScoped : ⊤G ⊢ S.pull D.DBAll
  elabScoped = S.pullTerm D.dbAll

  -- POSITIVE, MULTIPLICATIVELY, AWAY FROM THE BINDER.

  presVar : SplitPresAt dbCM varOp
  presVar .homSplit _ (mkVar n) = D.mkDVar (ρ₀ n)
  presVar .homParts _ (mkVar n) _ = Eq.refl

  presApp : SplitPresAt dbCM appOp
  presApp .homSplit _ (mkApp u v) = D.mkDApp (toDB ρ₀ u) (toDB ρ₀ v)
  presApp .homParts _ (mkApp u v) true  = Eq.refl
  presApp .homParts _ (mkApp u v) false = Eq.refl

  -- so the multiplicative fragment transports at those two
  pushˢ-var : {Q : (a : LAr varOp) → D.TheoryTy ℓ-zero (LSortOf varOp a)}
            → ⊗ˢ varOp (λ a → S.pull (Q a)) ⊢ S.pull (D.⊗ˢ varOp Q)
  pushˢ-var {Q} = S.push⊗ varOp presVar {B = Q}

  pushˢ-app : {Q : (a : LAr appOp) → D.TheoryTy ℓ-zero (LSortOf appOp a)}
            → ⊗ˢ appOp (λ a → S.pull (Q a)) ⊢ S.pull (D.⊗ˢ appOp Q)
  pushˢ-app {Q} = S.push⊗ appOp presApp {B = Q}

  -- ... and, spelled with each instance's own connective.
  pushVar : {P : D.NmG} → VarG (S.pull P) ⊢ S.pull (D.VarG P)
  pushVar {P} = pushˢ-var {Q = λ _ → P}

  pushApp : {A B : D.TmG} → AppG (S.pull A) (S.pull B) ⊢ S.pull (D.AppG A B)
  pushApp {A} {B} =
    pushˢ-app {Q = boolΠ {M = λ _ → D.TmG} A B}
    ∘g ⊗ˢ-map appOp {A = λ b → if b then S.pull A else S.pull B}
                    {B = λ b → S.pull (boolΠ {M = λ _ → D.TmG} A B b)}
                    (boolΠ {M = λ b → (if b then S.pull A else S.pull B)
                                        ⊢ S.pull (boolΠ {M = λ _ → D.TmG}
                                                          A B b)}
                             idg idg)

  -- REFLECTION, ALSO POSITIVE THERE. `toDB` sends each constructor to its
  -- namesake, so the head symbol of the output determines the head symbol
  -- of the input.

  reflVar : S.ReflectsSplitAt varOp
  reflVar (var n)   (D.mkDVar _)   = mkVar n , λ _ → Eq.refl
  reflVar (app u v) ()
  reflVar (lam n t) ()

  reflApp : S.ReflectsSplitAt appOp
  reflApp (var n)   ()
  reflApp (app u v) (D.mkDApp _ _) =
    mkApp u v
    , boolΠ {M = λ a → D.DBParts appOp (k , D.dapp (toDB ρ₀ u) (toDB ρ₀ v))
                              (D.mkDApp (toDB ρ₀ u) (toDB ρ₀ v)) a
                         Eq.≡ dbCM .hom (LSortOf appOp a)
                                 (LParts appOp (app u v) (mkApp u v) a)}
              Eq.refl Eq.refl
  reflApp (lam n t) ()

  -- so the tensor at those two operations is an ISOMORPHISM of
  -- grammars, not merely a lax map
  pullˢ-app : {Q : (a : LAr appOp) → D.TheoryTy ℓ-zero (LSortOf appOp a)}
            → S.pull (D.⊗ˢ appOp Q) ⊢ ⊗ˢ appOp (λ a → S.pull (Q a))
  pullˢ-app {Q} = S.pull⊗ appOp reflApp {B = Q}

  -- NEGATIVE, AT THE BINDER -- and that is the whole story.

  private
    lamFst : {j : ℕ} {t : D.DBTm j} (sp : D.IsDLam t)
           → fst (D.DBParts lamOp (j , t) sp false) ≡ suc j
    lamFst (D.mkDLam b) = refl

    noFix : (j : ℕ) → suc j ≡ j → ⊥
    noFix j p = ¬m<m (subst (j <_) p ≤-refl)

  ¬presLam : (n : Name) (t : Raw) → SplitPresAt dbCM lamOp → ⊥
  ¬presLam n t P =
    noFix k (sym (lamFst (P .homSplit (lam n t) (mkLam n t)))
             ∙ cong fst (Eq.eqToPath (P .homParts (lam n t) (mkLam n t) false)))

  -- reflection fails at the binder too, and for the same reason: the
  -- body of the elaborated term lives one scope up, so no splitting of
  -- the SOURCE can have parts matching it.
  ¬reflLam : (n : Name) (t : Raw) → S.ReflectsSplitAt lamOp → ⊥
  ¬reflLam n t R =
    noFix k (sym (lamFst (D.mkDLam (toDB (ext n ρ₀) t)))
             ∙ cong fst (Eq.eqToPath (R (lam n t)
                                        (D.mkDLam (toDB (ext n ρ₀) t))
                                        .snd false)))

  -- AND THE PAYOFF, in one line. `Check.linear?` decides linearity of a de
  -- Bruijn term INTERNALLY, as a map `⊤G ⊢ Dec⟨ Lin ⟩` over `dbFib`.

  linear? : ⊤G ⊢ Dec⟨ S.pull C.Lin ⟩
  linear? = S.pullTerm C.linear?
