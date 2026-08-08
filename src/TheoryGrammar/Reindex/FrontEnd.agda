{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE FRONT END AS A CHAIN OF LINKS. -}
module TheoryGrammar.Reindex.FrontEnd where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-comm)
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Nat.Order using (_<_; ¬m<m; suc-≤-suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.FinData.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.ChangeOfTheory
  using (SigMor; onSort; onOp; onAr; resEq; sortEq)
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Fibered using (module Terms)


import TheoryGrammar.Instances.LinLam.DB    as D
import TheoryGrammar.Instances.LinLam.Scope as SC
import TheoryGrammar.Instances.Heap.Graded  as H

open import TheoryGrammar.Instances.LinLam.Check using (Dec⊎; Join; join?)

open import TheoryGrammar.Reindex.LinLam
  using (dbTheory; fvLink; fvMap; λ→mon; fv; presApp?; presAppAt; presAppAt⁻;
         ¬presApp; ¬presVar; ¬reflApp)
open import TheoryGrammar.Reindex.Sanity
  using (linTheory; heapTheory; layoutPass)

-- §1  THE LAMBDA THEORY, BUNDLED.
--
-- `Instances.Spans` used to supply a stage 0 here, and §1 proved that
-- stage was not a `Pass` for ANY carrier map (`¬spanCatPres`: at the
-- degenerate cut the right slot of a span is the span itself).  Spans
-- are gone -- `Chain.Paren.Grammar` parses by `decμ` over `strFib` --
-- so that obstruction is gone with them, and every boundary named
-- below is a link.

module LamStage (Name : Type₀) where

  open Terms Name

  λTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
  λTheory = theory λSig λFib

-- §2 STAGE 1 IS A LINK, AND A PASS AT TWO OF THREE OPERATIONS.

module ScopeStage (Name : Type₀) (_≟_ : Discrete Name)
                  (k : ℕ) (ρ₀ : Name → Fin k) where

  open Terms Name
  open LamStage Name public using (λTheory)
  open SC.Elab Name _≟_ k ρ₀

  dbOver : ReindexOver (idSigMor λSig) λFib D.dbFib
  dbOver = ofReindex dbCM

  dbLink : Link λTheory dbTheory
  dbLink .sigL = idSigMor λSig
  dbLink .mapL = dbOver

  -- PRESERVATION, where it holds.  `presToOver` adds no coercion, so
  -- these are `Scope.presVar`/`presApp` by projection.
  dbPresVar : SplitPresAtOver dbOver varOp
  dbPresVar = presToOver dbCM varOp presVar

  dbPresApp : SplitPresAtOver dbOver appOp
  dbPresApp = presToOver dbCM appOp presApp

  -- ... AND REFLECTION, where it holds, with NOTHING written on the
  -- right: `ReflectsSplitAtOver` at `φ = id` IS `Along.ReflectsSplitAt`.
  dbReflVar : ReflectsSplitAtOver dbOver varOp
  dbReflVar = reflVar

  dbReflApp : ReflectsSplitAtOver dbOver appOp
  dbReflApp = reflApp

  -- the slot section is free at the identity signature morphism
  dbSection : (o : LOp) → ArSection (idSigMor λSig) o
  dbSection = idArSection λSig

  -- THE OBSTRUCTION, restated over the signature morphism.
  ¬dbPresLam : (n : Name) (t : Raw) → SplitPresAtOver dbOver lamOp → ⊥
  ¬dbPresLam n t P = ¬presLam n t (presFromOver dbCM lamOp P)

  ¬dbReflLam : (n : Name) (t : Raw) → ReflectsSplitAtOver dbOver lamOp → ⊥
  ¬dbReflLam = ¬reflLam

  -- so it is a LINK and not a PASS, and that is exactly one operation's
  -- worth of failure.
  ¬dbPass : (n : Name) (t : Raw)
          → ((o : LOp) → SplitPresAtOver dbOver o) → ⊥
  ¬dbPass n t P = ¬dbPresLam n t (P lamOp)

  -- §3 THE FRONT END, COMPOSED. Raw --toDB--> de Bruijn --fv--> usage
  -- --layout--> heap Three links, two of which cross a signature (`λSig →
  -- monoidSig` at the second, nothing at the first and third), one of
  -- which is a verified `Pass` with its verification forgotten.

  frontLink : Link λTheory heapTheory
  frontLink = dbLink ⨟L fvLink ⨟L forget layoutPass

  -- the composite's signature morphism, spelled out
  _ : frontLink .sigL .onOp appOp ≡ H.appop
  _ = refl

  _ : frontLink .sigL .onOp lamOp ≡ H.nilop
  _ = refl

  _ : frontLink .sigL .onSort tm ≡ tt
  _ = refl

  -- ... and the prefix that stops at usages, which is the stage
  -- `LinLam.Check` decides over
  usageLink : Link λTheory linTheory
  usageLink = dbLink ⨟L fvLink

  -- WHAT THE LINK BUYS WITH NO PRESERVATION: the additive fragment, across
  -- all three boundaries at once.

  module FE  = AlongOver (frontLink .mapL)
  module Src = FibNotation λFib
  module Tgt = FibNotation H.heapFib

  frontPull : Tgt.TheoryTy ℓ-zero tt → Src.TheoryTy ℓ-zero tm
  frontPull B = FE.pullO {s = tm} B

  frontPullTerm : {A B : Tgt.TheoryTy ℓ-zero tt}
                → A Tgt.⊢ B → frontPull A Src.⊢ frontPull B
  frontPullTerm f = FE.pullTermO {s = tm} f

  -- the additives are preserved ON THE NOSE, and that is `refl`
  _ : frontPull (Tgt.⊤G {s = tt}) ≡ Src.⊤G {s = tm}
  _ = refl

-- §4 WHERE THE `fv` LINK BECOMES A PASS, TERM BY TERM.

linkIsPassAt? : (n : ℕ) (u v : D.DBTm n)
              → Dec⊎ (PresAt fvMap appOp (n , D.dapp u v))
linkIsPassAt? = presApp?

linkPassAt : (n : ℕ) (u v : D.DBTm n)
           → Join (fv u) (fv v) → PresAt fvMap appOp (n , D.dapp u v)
linkPassAt = presAppAt

linkPassAt⁻ : (n : ℕ) (u v : D.DBTm n)
            → PresAt fvMap appOp (n , D.dapp u v) → Join (fv u) (fv v)
linkPassAt⁻ = presAppAt⁻

-- §5  IT COMPUTES.  A RAW NAMED TERM to the heap frame of its free
-- variables, through three signature translations and four theories.
-- If any `Eq`-world bookkeeping had gone inert these would be stuck.

module FrontEndTests where

  ρ2 : ℕ → Fin 2
  ρ2 zero    = fzero
  ρ2 (suc _) = fsuc fzero

  open Terms ℕ
  open ScopeStage ℕ discreteℕ 2 ρ2

  -- two distinct free variables lay out to two disjoint cells
  _ : frontLink .mapL .homO tm (app (var 0) (var 1))
    ≡ (0 , H.v1) ∷ (1 , H.v1) ∷ []
  _ = refl

  -- ... and the non-linear term collapses them onto one, which is the
  -- computational shadow of `¬presApp`
  _ : frontLink .mapL .homO tm (app (var 0) (var 0)) ≡ H.single 0 H.v1
  _ = refl

  -- a bound occurrence allocates nothing
  _ : frontLink .mapL .homO tm (lam 0 (var 0)) ≡ []
  _ = refl

  -- ... and a lambda with a free body does allocate, which is why the
  -- composite cannot preserve at `lamOp` (whose image is `nilop`, whose
  -- splitting is `IsNil`)
  _ : frontLink .mapL .homO tm (lam 0 (var 1)) ≡ (1 , H.v1) ∷ []
  _ = refl

  -- THE COMPOSITE FAILS AT THE BINDER, with that as the witness:
  -- `nilop`'s splitting of a non-empty heap is `⊥`.
  ¬frontPresLam : SplitPresAtOver (frontLink .mapL) lamOp → ⊥
  ¬frontPresLam P = P .homSplitO (lam 0 (var 1)) (mkLam 0 (var 1))
