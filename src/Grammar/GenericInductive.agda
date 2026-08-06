{-
  The inductive-grammar machinery, generic in the signature.

  This is Grammar.Inductive.Functor with exactly one constructor
  changed: `_⊗e_ : F → F → F` (binary, because concatenation is) becomes

      ⊗e : (o : Op) → ((a : arity o) → SPF …) → SPF …

  i.e. one n-ary tensor per operation of the signature.  Everything
  else -- k, Var, ⊕e, &e -- never mentioned the substrate.

  A signature is an indexed container: at index m, the shapes of ⊗e o
  are the splittings `Σ m⃗. Split o m⃗ m`, the positions are `arity o`,
  and position `a` points at index `m⃗ a`.
-}
module Grammar.GenericInductive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
-- (same records as Grammar.GenericSyntax; repeated so this module does
-- not depend on that one's unfinished soundness proof)
record Sig ℓ : Type (ℓ-suc ℓ) where
  field
    Sort    : Type ℓ
    Op      : Type ℓ
    arity   : Op → Type ℓ
    argSort : (o : Op) → arity o → Sort
    resSort : Op → Sort

open Sig

record Base {ℓ} (Σ : Sig ℓ) : Type (ℓ-suc ℓ) where
  field
    carrier : Σ .Sort → Type ℓ
    Split   : (o : Σ .Op)
            → ((a : Σ .arity o) → carrier (Σ .argSort o a))
            → carrier (Σ .resSort o) → Type ℓ

open Base

module Generic {ℓ} (Σ : Sig ℓ) (B : Base Σ) where

  Gr : Σ .Sort → Type (ℓ-suc ℓ)
  Gr s = B .carrier s → Type ℓ

  -- X : the mutually-defined nonterminals; xs assigns each a sort
  data SPF (X : Type ℓ) (xs : X → Σ .Sort) : Σ .Sort → Type (ℓ-suc ℓ) where
    k   : ∀ {s} → Gr s → SPF X xs s
    Var : (x : X) → SPF X xs (xs x)
    ⊕e  : ∀ {s} (Y : Type ℓ) → (Y → SPF X xs s) → SPF X xs s
    &e  : ∀ {s} (Y : Type ℓ) → (Y → SPF X xs s) → SPF X xs s
    ⊗e  : (o : Σ .Op)
        → ((a : Σ .arity o) → SPF X xs (Σ .argSort o a))
        → SPF X xs (Σ .resSort o)

  module _ {X : Type ℓ} {xs : X → Σ .Sort} where

    ⟦_⟧F : ∀ {s} → SPF X xs s → ((x : X) → Gr (xs x)) → Gr s
    ⟦ k A     ⟧F P m = A m
    ⟦ Var x   ⟧F P m = P x m
    ⟦ ⊕e Y F  ⟧F P m = Σ[ y ∈ Y ] ⟦ F y ⟧F P m
    ⟦ &e Y F  ⟧F P m = (y : Y) → ⟦ F y ⟧F P m
    ⟦ ⊗e o F  ⟧F P m =
      Σ[ m⃗ ∈ ((a : Σ .arity o) → B .carrier (Σ .argSort o a)) ]
        (B .Split o m⃗ m × ((a : Σ .arity o) → ⟦ F a ⟧F P (m⃗ a)))

    -- the initial algebra
    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : (x : X) → SPF X xs (xs x)) : (x : X) → Gr (xs x) where
      roll : ∀ {x m} → ⟦ F x ⟧F (μ F) m → μ F x m

    module _ {F : (x : X) → SPF X xs (xs x)}
             {A : (x : X) → Gr (xs x)}
             (α : ∀ x m → ⟦ F x ⟧F A m → A x m) where

      -- The recursor, mutually with its action on the functor syntax.
      -- TERMINATING for exactly the reason Grammar.Inductive.Indexed
      -- needs it: the recursive occurrence is a component of `t` but
      -- sits under the defined function ⟦_⟧F, which the checker cannot
      -- see through.  The principled fix is the same for both: rank the
      -- container by the substrate's degree.
      {-# TERMINATING #-}
      rec  : ∀ x m → μ F x m → A x m
      {-# TERMINATING #-}
      recF : ∀ {s} (G : SPF X xs s) m → ⟦ G ⟧F (μ F) m → ⟦ G ⟧F A m

      rec x m (roll t) = α x m (recF (F x) m t)

      recF (k C)    m t             = t
      recF (Var x)  m t             = rec x m t
      recF (⊕e Y G) m (y , t)       = y , recF (G y) m t
      recF (&e Y G) m f             = λ y → recF (G y) m (f y)
      recF (⊗e o G) m (m⃗ , sp , f)  = m⃗ , sp , λ a → recF (G a) (m⃗ a) (f a)

-- ==================================================================
-- Instantiation: the lambda signature.  `Scoped` becomes a μ whose
-- NONTERMINALS ARE THE SCOPES -- X = Scope, and the lam case refers to
-- `Var (n ∷ Γ)`.  Compare Grammar.LambdaScope, where the same family
-- was a hand-written Agda inductive.
-- ==================================================================

module LambdaInstance (Name : Type ℓ-zero) where

  open import Cubical.Data.Unit
  open import Cubical.Data.Bool
  open import Cubical.Data.Empty
  open import Cubical.Data.Sum
  open import Cubical.Data.List
  import Cubical.Data.Equality as Eq

  data Raw : Type ℓ-zero where
    var : Name → Raw
    app : Raw → Raw → Raw
    lam : Name → Raw → Raw

  data LOp : Type ℓ-zero where
    varOp : Name → LOp
    appOp : LOp
    lamOp : Name → LOp

  LSig : Sig ℓ-zero
  LSig .Sort          = Unit
  LSig .Op            = LOp
  LSig .arity (varOp n) = ⊥
  LSig .arity appOp     = Bool
  LSig .arity (lamOp n) = Unit
  LSig .argSort o a   = tt
  LSig .resSort o     = tt

  LBase : Base LSig
  LBase .carrier _              = Raw
  LBase .Split (varOp n) m⃗ m = m Eq.≡ var n
  LBase .Split appOp     m⃗ m = m Eq.≡ app (m⃗ false) (m⃗ true)
  LBase .Split (lamOp n) m⃗ m = m Eq.≡ lam n (m⃗ tt)

  open Generic LSig LBase

  Scope : Type ℓ-zero
  Scope = List Name

  _∈_ : Name → Scope → Type ℓ-zero
  n ∈ []      = ⊥
  n ∈ (m ∷ Γ) = (n ≡ m) ⊎ (n ∈ Γ)

  -- one nonterminal per scope
  ScopedF : Scope → SPF Scope (λ _ → tt) tt
  ScopedF Γ = ⊕e (Name ⊎ (Unit ⊎ Name)) alt
    where
      alt : Name ⊎ (Unit ⊎ Name) → SPF Scope (λ _ → tt) tt
      alt (inl n)             = ⊕e (n ∈ Γ) λ _ → ⊗e (varOp n) λ ()
      alt (inr (inl _))       = ⊗e appOp λ _ → Var Γ
      alt (inr (inr n))       = ⊗e (lamOp n) λ _ → Var (n ∷ Γ)

  Scoped : Scope → Raw → Type ℓ-zero
  Scoped = μ ScopedF

-- ------------------------------------------------------------------
-- It is usable: a derivation that λx.x is closed, built in the
-- generic μ rather than in a bespoke datatype.
-- ------------------------------------------------------------------

module LambdaTest where

  open import Cubical.Data.Nat
  open import Cubical.Data.Sum
  open import Cubical.Data.List
  open import Cubical.Data.Unit
  import Cubical.Data.Equality as Eq
  open LambdaInstance ℕ
  open Generic LSig LBase

  idClosed : Scoped [] (lam 0 (var 0))
  idClosed =
    roll ( inr (inr 0)
         , (λ _ → var 0)
         , Eq.refl
         , λ _ → roll (inl 0 , inl refl , (λ ()) , Eq.refl , λ ()) )
