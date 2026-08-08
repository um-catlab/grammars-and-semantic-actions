{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- IS THIS BRIDGE A PASS? SEARCHED FOR, NOT GUESSED. -}
module TheoryGrammar.Refute where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.ChangeOfTheory using (SigMor; onOp; onAr)
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed

private variable
  ℓS ℓS' ℓ ℓ' ℓ2 ℓ2' ℓX ℓX' ℓP ℓP' ℓI ℓB : Level

-- 0. THE SEARCH.

searchNo : {I : Type ℓI} {B : I → Type ℓB}
         → ((i : I) → B i ⊎ No (B i)) → List I
         → Maybe (Σ[ i ∈ I ] No (B i))
searchNo d []       = nothing
searchNo d (i ∷ is) = pick (d i)
  where pick : _ → _
        pick (inl _) = searchNo d is
        pick (inr k) = just (i , k)

-- 1.  ONE FAILING POINT KILLS THE OPERATION.

module RefuteAt {S : Type ℓS} {S' : Type ℓS'}
                {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
                {φ : SigMor σ τ}
                {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered τ ℓX' ℓP'}
                (h : ReindexOver φ Fib Fib') (o : σ .ops)
                where

  private
    Pt : Type ℓX
    Pt = Fib .carrier (σ .resultSort o)

  -- 1a.  PRESERVATION.  `¬presApp`, `¬presVar`, `¬presLam` and
  -- `noPackPres` are all this, at their point.

  presNo : (m : Pt) → No (PresAt h o m) → No (SplitPresAtOver h o)
  presNo m k P = k (fromPres h o P m)

  refutePres : (Σ[ m ∈ Pt ] No (PresAt h o m)) → No (SplitPresAtOver h o)
  refutePres (m , k) = presNo m k

  -- 1b. REFLECTION.

  ReflAt : (m : Pt) → Type (ℓ-max ℓ2' (ℓ-max ℓX' (ℓ-max ℓP ℓP')))
  ReflAt m =
    (sp' : Fib' .Split (φ .onOp o) (homAtOf h o m))
    → Σ[ sp ∈ Fib .Split o m ]
        ((b : τ .arities (φ .onOp o))
         → Fib' .parts (φ .onOp o) (homAtOf h o m) sp' b
           Eq.≡ homSlotOf h o b (Fib .parts o m sp (φ .onAr o b)))

  refl-is-Π : ReflectsSplitAtOver h o ≡ ((m : Pt) → ReflAt m)
  refl-is-Π = refl

  reflNo : (m : Pt) → No (ReflAt m) → No (ReflectsSplitAtOver h o)
  reflNo m k R = k (R m)

  refuteRefl : (Σ[ m ∈ Pt ] No (ReflAt m)) → No (ReflectsSplitAtOver h o)
  refuteRefl (m , k) = reflNo m k

  -- 2.  THE VERDICT.  Asymmetric ON PURPOSE -- see the header.

  data Verdict : Type (ℓ-max ℓX (ℓ-max ℓ2' (ℓ-max ℓX' (ℓ-max ℓP ℓP')))) where
    -- the point, AND the theorem it proves
    refuted  : (m : Pt) → No (SplitPresAtOver h o) → Verdict
    -- how many points were tried.  NOT a proof of anything.
    survived : ℕ → Verdict

  scanPres : ((m : Pt) → PresAt h o m ⊎ No (PresAt h o m))
           → List Pt → Verdict
  scanPres d space = out (searchNo d space)
    where out : _ → Verdict
          out nothing        = survived (length space)
          out (just (m , k)) = refuted m (presNo m k)

  -- the point that failed, for a `refl` test.  The refutation itself is
  -- a function and so is not comparable; the point is.
  culprit : Verdict → Maybe Pt
  culprit (refuted m _) = just m
  culprit (survived _)  = nothing

  tried : Verdict → ℕ
  tried (refuted _ _) = 0
  tried (survived n)  = n

  -- ... AND THE VERDICT USED AS A THEOREM.

  Refutes : Verdict → Type₀
  Refutes (refuted _ _) = Unit
  Refutes (survived _)  = ⊥

  theorem : (v : Verdict) → Refutes v → No (SplitPresAtOver h o)
  theorem (refuted _ k) _ = k

  -- ... and the same for reflection
  data VerdictR : Type (ℓ-max ℓX (ℓ-max ℓ2' (ℓ-max ℓX' (ℓ-max ℓP ℓP')))) where
    refutedR  : (m : Pt) → No (ReflectsSplitAtOver h o) → VerdictR
    survivedR : ℕ → VerdictR

  scanRefl : ((m : Pt) → ReflAt m ⊎ No (ReflAt m)) → List Pt → VerdictR
  scanRefl d space = out (searchNo d space)
    where out : _ → VerdictR
          out nothing        = survivedR (length space)
          out (just (m , k)) = refutedR m (reflNo m k)

  culpritR : VerdictR → Maybe Pt
  culpritR (refutedR m _) = just m
  culpritR (survivedR _)  = nothing

  RefutesR : VerdictR → Type₀
  RefutesR (refutedR _ _) = Unit
  RefutesR (survivedR _)  = ⊥

  theoremR : (v : VerdictR) → RefutesR v → No (ReflectsSplitAtOver h o)
  theoremR (refutedR _ k) _ = k

  -- 3. THE OTHER HALF, AND WHAT IT COSTS.

  provePres : Listed Pt
            → ((m : Pt) → PresAt h o m ⊎ No (PresAt h o m))
            → SplitPresAtOver h o ⊎ No (SplitPresAtOver h o)
  provePres L d = out (findΠ (L .elts) (L .complete) d)
    where out : _ → _
          out (inl f)       = inl (toPres h o f)
          out (inr (m , k)) = inr (presNo m k)
