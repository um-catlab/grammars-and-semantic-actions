{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- LEVI IS AN AXIOM, NOT A THEOREM. `Refinement.Refinable` is stated for
   every theory and proved in five instances, so it is fair to ask whether
   some general principle gives it. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.NoRefine where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Refinement
open import TheoryGrammar.Precision using (coeEq)

open import TheoryGrammar.Instances.Nat.Base
  using (MonOp; nilop; appop; MonAr; monoidSig; Add3; z; s; addAll; IsZero)

-- 1.  THE SEMIGROUP.  `Gap` is Unit/⊥-valued, so membership is
--     definitionally propositional and every test below reduces.

Gap : ℕ → Type₀
Gap zero                = Unit
Gap (suc zero)          = ⊥                        -- the gap
Gap (suc (suc _))       = Unit

-- PRIMITIVE.  Closure under addition -- what makes it a submonoid.
gap+ : (a b : ℕ) → Gap a → Gap b → Gap (a + b)
gap+ zero          b ga gb = gb
gap+ (suc zero)    b ga gb = E.rec ga
gap+ (suc (suc a)) b ga gb = tt

Gp : Type₀
Gp = Σ[ n ∈ ℕ ] Gap n

-- 2.  THE `Fibered`, and its TOTAL point.  Nothing here is partial:
--     `gapPoint` is the whole reason this counterexample is worth
--     having rather than an ad-hoc set of formal splittings.

GapSplit : (o : MonOp) → Gp → Type₀
GapSplit nilop g = IsZero (g .fst)
GapSplit appop g = Σ[ u ∈ Gp ] Σ[ v ∈ Gp ] Add3 (u .fst) (v .fst) (g .fst)

GapParts : (o : MonOp) (g : Gp) → GapSplit o g → MonAr o → Gp
GapParts nilop g sp ()
GapParts appop g (u , v , _) b = if b then u else v

gapFib : Fibered monoidSig ℓ-zero ℓ-zero
gapFib .carrier _ = Gp
gapFib .Split     = GapSplit
gapFib .parts     = GapParts

gapPoint : LaxPoint gapFib
gapPoint .op nilop _ = 0 , tt
gapPoint .op appop f =
  (f true .fst + f false .fst) , gap+ _ _ (f true .snd) (f false .snd)
gapPoint .split nilop f = tt
gapPoint .split appop f = f true , f false , addAll (f true .fst) (f false .fst)
gapPoint .parts-split nilop f = funExt λ ()
gapPoint .parts-split appop f = funExt λ { false → refl ; true → refl }

open Refine gapFib

addHom : HomOp tt
addHom .op⋆    = appop
addHom .resH   = Eq.refl
addHom .argH _ = Eq.refl

-- 3.  DISCRIMINATION.  Unit/⊥-valued, so `NEq 2 3` IS `⊥`.

NEq : ℕ → ℕ → Type₀                                -- PRIMITIVE
NEq zero    zero    = Unit
NEq zero    (suc _) = ⊥
NEq (suc _) zero    = ⊥
NEq (suc m) (suc n) = NEq m n

nrefl : (n : ℕ) → NEq n n                          -- PRIMITIVE
nrefl zero    = tt
nrefl (suc n) = nrefl n

nabsurd : {m n : ℕ} → m Eq.≡ n → NEq m n
nabsurd {m} e = coeEq (NEq m) e (nrefl m)

-- 4. THE ARITHMETIC, stated without mentioning the framework.

two-cases : (x y : ℕ) → Gap x → Gap y → Add3 x y 2 → (x Eq.≡ 0) ⊎ (x Eq.≡ 2)
two-cases _ _ gx gy z         = inl Eq.refl
two-cases _ _ gx gy (s z)     = E.rec gx           -- x = 1
two-cases _ _ gx gy (s (s z)) = inr Eq.refl

three-cases : (u w : ℕ) → Gap u → Gap w → Add3 u w 3
            → ((u Eq.≡ 0) × (w Eq.≡ 3)) ⊎ ((u Eq.≡ 3) × (w Eq.≡ 0))
three-cases _ _ gu gw z             = inl (Eq.refl , Eq.refl)
three-cases _ _ gu gw (s z)         = E.rec gu     -- u = 1
three-cases _ _ gu gw (s (s z))     = E.rec gw     -- w = 1
three-cases _ _ gu gw (s (s (s z))) = inr (Eq.refl , Eq.refl)

-- 4 = 3 + 1 is not a decomposition, because 1 is not there
no-3+ : (b : ℕ) → Gap b → Add3 3 b 4 → ⊥
no-3+ _ gb (s (s (s z))) = gb

-- THE CLASH, as pure arithmetic: a 2x2 matrix over <2,3> whose first
-- row sums to 2, first column to 3 and second row to 4 cannot exist.
key : (x y : ℕ) → Gap x → Gap y → Add3 x y 2            -- row 0 of the matrix
    → (u w : ℕ) → Gap u → Gap w → Add3 u w 3            -- column 0
    → (m n : ℕ) → Gap n → Add3 m n 4                    -- row 1
    → x Eq.≡ u                                          -- both are cell(0,0)
    → m Eq.≡ w                                          -- both are cell(1,0)
    → ⊥
key x y gx gy a2 u w gu gw a3 m n gn a4 exu emw =
  go (two-cases x y gx gy a2) (three-cases u w gu gw a3)
  where
  go : (x Eq.≡ 0) ⊎ (x Eq.≡ 2)
     → ((u Eq.≡ 0) × (w Eq.≡ 3)) ⊎ ((u Eq.≡ 3) × (w Eq.≡ 0))
     → ⊥
  -- cell(0,0) = 0, so cell(1,0) = 3 and row 1 needs a 1
  go (inl _)  (inl (_ , e3)) =
    no-3+ n gn (coeEq (λ k → Add3 k n 4) (Eq._∙_ emw e3) a4)
  -- the three ways the two readings of cell(0,0) disagree outright
  go (inl e0) (inr (e3 , _)) = nabsurd (Eq._∙_ (Eq._∙_ (Eq.sym e0) exu) e3)
  go (inr e2) (inl (e0 , _)) = nabsurd (Eq._∙_ (Eq._∙_ (Eq.sym e2) exu) e0)
  go (inr e2) (inr (e3 , _)) = nabsurd (Eq._∙_ (Eq._∙_ (Eq.sym e2) exu) e3)

-- 5.  THE THEOREM.

six : Gp
six = 6 , tt

p6 : SplitH addHom six            -- 6 = 2 + 4
p6 = (2 , tt) , (4 , tt) , s (s z)

q6 : SplitH addHom six            -- 6 = 3 + 3
q6 = (3 , tt) , (3 , tt) , s (s (s z))

noRefine : Refinable addHom addHom → ⊥
noRefine ref =
  key (r0 .fst .fst) (r0 .snd .fst .fst) (r0 .fst .snd) (r0 .snd .fst .snd)
      (r0 .snd .snd)
      (k0 .fst .fst) (k0 .snd .fst .fst) (k0 .fst .snd) (k0 .snd .fst .snd)
      (k0 .snd .snd)
      (r1 .fst .fst) (r1 .snd .fst .fst) (r1 .snd .fst .snd)
      (r1 .snd .snd)
      (Eq.ap fst (Eq._∙_ (R .rowCell true true)
                         (Eq.sym (R .colCell true true))))
      (Eq.ap fst (Eq._∙_ (R .rowCell false true)
                         (Eq.sym (R .colCell true false))))
  where
  R  = ref six p6 q6
  r0 = R .rowSplit true             -- splits 2 into cells (0,0) and (0,1)
  k0 = R .colSplit true             -- splits 3 into cells (0,0) and (1,0)
  r1 = R .rowSplit false            -- splits 4 into cells (1,0) and (1,1)

-- 6. ... AND THE ENCODING IS NOT THE PROBLEM.

zeroG : Gp
zeroG = 0 , tt

addNilR : (m : ℕ) → Add3 m 0 m
addNilR zero    = z
addNilR (suc m) = s (addNilR m)

diagCell : (m : Gp) (p : SplitH addHom m) → Bool → Bool → Gp
diagCell m p true  true  = GapParts appop m p true
diagCell m p true  false = zeroG
diagCell m p false true  = zeroG
diagCell m p false false = GapParts appop m p false

diagRef : (m : Gp) (p : SplitH addHom m) → Refinement addHom addHom m p p
diagRef m p .cell                = diagCell m p
diagRef m p .rowSplit true       = GapParts appop m p true , zeroG , addNilR _
diagRef m p .rowSplit false      = zeroG , GapParts appop m p false , z
diagRef m p .rowCell true  true  = Eq.refl
diagRef m p .rowCell true  false = Eq.refl
diagRef m p .rowCell false true  = Eq.refl
diagRef m p .rowCell false false = Eq.refl
diagRef m p .colSplit true       = GapParts appop m p true , zeroG , addNilR _
diagRef m p .colSplit false      = zeroG , GapParts appop m p false , z
diagRef m p .colCell true  true  = Eq.refl
diagRef m p .colCell true  false = Eq.refl
diagRef m p .colCell false true  = Eq.refl
diagRef m p .colCell false false = Eq.refl
