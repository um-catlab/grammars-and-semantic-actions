{-
  Instances of the generic layer, with `Base` as a CONTAINER: shapes
  indexed by the output, components as projections.

  This is the fix for the blocker.  Indexing `Split` by the components
  made them neutral terms and every inversion got stuck.  Indexing by the
  OUTPUT makes `Split o m` an ordinary inductive family the substrate can
  case-split on, and `parts` computes on its constructors -- so the
  Brzozowski case split is available again.
-}
module Grammar.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥; ⊥*)

open import Grammar.GenericContainer

-- ==================================================================
-- INSTANCE 1.  (ℕ, +) with a unary successor -- combinatorics.
-- ==================================================================

module Comb where

  data Cut : ℕ → Type₀ where
    here  : ∀ {n} → Cut n
    there : ∀ {n} → Cut n → Cut (suc n)

  cutL cutR : ∀ {n} → Cut n → ℕ
  cutL here       = 0
  cutL (there k)  = suc (cutL k)
  cutR (here {n}) = n
  cutR (there k)  = cutR k

  data IsSuc : ℕ → Type₀ where mkS : ∀ {n} → IsSuc (suc n)
  prd : ∀ {n} → IsSuc n → ℕ
  prd (mkS {n}) = n

  CombSig : Sig ℓ-zero
  CombSig .Sig.Sort        = Unit
  CombSig .Sig.Op          = Bool
  CombSig .Sig.arity false = Bool
  CombSig .Sig.arity true  = Unit
  CombSig .Sig.argSort _ _ = tt
  CombSig .Sig.resSort _   = tt

  CombBase : Base CombSig
  CombBase .Base.carrier _ = ℕ
  CombBase .Base.Split false n = Cut n
  CombBase .Base.Split true  n = IsSuc n
  CombBase .Base.parts false n k false = cutL k
  CombBase .Base.parts false n k true  = cutR k
  CombBase .Base.parts true  n s _     = prd s

  open Generic CombSig CombBase
  open Fam Unit (λ _ → tt) public

  data Ε : ℕ → Type₀ where mkΕ : Ε 0

  BinF : Unit → SPF tt
  BinF _ = ⊕e Bool alt
    where
      alt : Bool → SPF tt
      alt false = k Ε
      alt true  = ⊗e true (λ _ → ⊗e false (λ _ → Var tt))

  Bin : ℕ → Type₀
  Bin n = μ BinF (tt , n)

  -- Catalan recurrence, from the generic unroll.  The splitting is now
  -- first-class, so it appears in the statement directly.
  catalan : ∀ n → Bin (suc n) → Σ[ c ∈ Cut n ] (Bin (cutL c) × Bin (cutR c))
  catalan n t with unroll t
  ... | (false , ()) , f
  ... | (true , mkS , shs) , f =
    shs tt .fst , f (tt , false , tt*) , f (tt , true , tt*)

-- ==================================================================
-- INSTANCE 2.  Strings -- the case split that was stuck.
-- ==================================================================

module Str (Al : Type₀) (A : List Al → Type₀) where

  data Cut : List Al → Type₀ where
    here  : ∀ {w} → Cut w
    there : ∀ {c w} → Cut w → Cut (c ∷ w)

  cutL cutR : ∀ {w} → Cut w → List Al
  cutL here          = []
  cutL (there {c} k) = c ∷ cutL k
  cutR (here {w})    = w
  cutR (there k)     = cutR k

  StrSig : Sig ℓ-zero
  StrSig .Sig.Sort        = Unit
  StrSig .Sig.Op          = Unit
  StrSig .Sig.arity   _   = Bool
  StrSig .Sig.argSort _ _ = tt
  StrSig .Sig.resSort _   = tt

  StrBase : Base StrSig
  StrBase .Base.carrier _ = List Al
  StrBase .Base.Split _ w = Cut w
  StrBase .Base.parts _ w k false = cutL k
  StrBase .Base.parts _ w k true  = cutR k

  open Generic StrSig StrBase
  open Fam Unit (λ _ → tt) public

  data Ες : List Al → Type₀ where mkΕ : Ες []

  StarF : Unit → SPF tt
  StarF _ = ⊕e Bool alt
    where
      alt : Bool → SPF tt
      alt false = k Ες
      alt true  = ⊗e tt (λ { false → k A ; true → Var tt })

  KStar : List Al → Type₀
  KStar w = μ StarF (tt , w)

  -- THE STAR DERIVATIVE.  `Cut (c ∷ w)` has exactly two constructors,
  -- so this is the Brzozowski case split -- stuck under the old Base.
  δ* : ∀ c w → KStar (c ∷ w)
     → Σ[ cu ∈ Cut w ] (A (c ∷ cutL cu) × KStar (cutR cu))
  δ* c w (sup (false , ()) f)
  δ* c w (sup (true , here    , shs) f) = δ* c w (f (true , tt*))
  δ* c w (sup (true , there cu , shs) f) = cu , shs false , f (true , tt*)

-- ==================================================================
-- INSTANCE 3.  Lambda ASTs.  Every splitting relation is an ordinary
-- inductive family indexed by the OUTPUT term, so `parts` computes by
-- matching on it.
-- ==================================================================

module Lam (Name : Type₀) where

  data Raw : Type₀ where
    var : Name → Raw
    app : Raw → Raw → Raw
    lam : Name → Raw → Raw

  data LOp : Type₀ where
    varOp : Name → LOp
    appOp : LOp
    lamOp : Name → LOp

  data IsVar (n : Name) : Raw → Type₀ where mkV : IsVar n (var n)
  data IsApp             : Raw → Type₀ where mkA : ∀ {u v} → IsApp (app u v)
  data IsLam (n : Name) : Raw → Type₀ where mkL : ∀ {t} → IsLam n (lam n t)

  LSig : Sig ℓ-zero
  LSig .Sig.Sort            = Unit
  LSig .Sig.Op              = LOp
  LSig .Sig.arity (varOp n) = ⊥
  LSig .Sig.arity appOp     = Bool
  LSig .Sig.arity (lamOp n) = Unit
  LSig .Sig.argSort _ _     = tt
  LSig .Sig.resSort _       = tt

  LBase : Base LSig
  LBase .Base.carrier _ = Raw
  LBase .Base.Split (varOp n) m = IsVar n m
  LBase .Base.Split appOp     m = IsApp m
  LBase .Base.Split (lamOp n) m = IsLam n m
  LBase .Base.parts (varOp n) m s ()
  LBase .Base.parts appOp     _ (mkA {u} {v}) false = u
  LBase .Base.parts appOp     _ (mkA {u} {v}) true  = v
  LBase .Base.parts (lamOp n) _ (mkL {t}) _         = t

  Scope : Type₀
  Scope = List Name

  _∈_ : Name → Scope → Type₀
  n ∈ []      = ⊥
  n ∈ (m ∷ Γ) = (n ≡ m) ⊎ (n ∈ Γ)

  open Generic LSig LBase
  open Fam Scope (λ _ → tt) public

  -- nonterminals ARE the scopes
  ScopedF : Scope → SPF tt
  ScopedF Γ = ⊕e (Name ⊎ (Unit ⊎ Name)) alt
    where
      alt : Name ⊎ (Unit ⊎ Name) → SPF tt
      alt (inl n)       = ⊕e (n ∈ Γ) λ _ → ⊗e (varOp n) λ ()
      alt (inr (inl _)) = ⊗e appOp λ _ → Var Γ
      alt (inr (inr n)) = ⊗e (lamOp n) λ _ → Var (n ∷ Γ)

  Scoped : Scope → Raw → Type₀
  Scoped Γ t = μ ScopedF (Γ , t)

  -- de Bruijn elaboration as an ALGEBRA for the grammar functor
  data Idx : ℕ → Type₀ where
    zero : ∀ {n} → Idx (suc n)
    suc  : ∀ {n} → Idx n → Idx (suc n)

  data DB : ℕ → Type₀ where
    dvar : ∀ {n} → Idx n → DB n
    dapp : ∀ {n} → DB n → DB n → DB n
    dlam : ∀ {n} → DB (suc n) → DB n

  ix : ∀ {n Γ} → n ∈ Γ → Idx (length Γ)
  ix {Γ = m ∷ Γ} (inl _) = zero
  ix {Γ = m ∷ Γ} (inr i) = suc (ix i)

  Mot : Ix → Type₀
  Mot (Γ , t) = DB (length Γ)

  α : ∀ Γ t (sh : Sh (ScopedF Γ) t)
    → ((p : Pos (ScopedF Γ) t sh) → Mot (nx (ScopedF Γ) t sh p))
    → DB (length Γ)
  α Γ t (inl n , i , _)   f = dvar (ix i)
  α Γ t (inr (inl _) , _) f = dapp (f (false , tt*)) (f (true , tt*))
  α Γ t (inr (inr n) , _) f = dlam (f (tt , tt*))

  toDB : ∀ Γ t → Scoped Γ t → DB (length Γ)
  toDB Γ t = fold α (Γ , t)
