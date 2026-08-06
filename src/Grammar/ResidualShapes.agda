module Grammar.ResidualShapes where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Grammar.GenericContainer

module R {ℓ} (Σ : Sig ℓ) (B : Base Σ) where
  open Sig ; open Base
  Gr : Σ .Sort → Type (ℓ-suc ℓ)
  Gr s = B .carrier s → Type ℓ

  -- The JOINT residual: reindexing along the splitting projection.
  -- Its domain is the total space of SPLITTINGS, not any component.
  -- No holes, no arity arithmetic, no equations.
  Splittings : Σ .Op → Type ℓ
  Splittings o = Σ[ m ∈ B .carrier (Σ .resSort o) ] B .Split o m

  ⊸joint : (o : Σ .Op) → Gr (Σ .resSort o) → Splittings o → Type ℓ
  ⊸joint o Q (m , sp) = Q m

  -- A residual with SOME positions left open: J says which.
  -- The equation `parts … a ≡ g a` is the residue: a splitting fixes
  -- ALL components, but we want to constrain only the open ones.
  ⊸open : (o : Σ .Op) (J : Σ .arity o → Type ℓ)
        → ((a : Σ .arity o) → Gr (Σ .argSort o a))
        → Gr (Σ .resSort o)
        → ((a : Σ .arity o) → J a → B .carrier (Σ .argSort o a)) → Type ℓ
  ⊸open o J A Q g =
    (m : B .carrier (Σ .resSort o)) (sp : B .Split o m)
    → ((a : Σ .arity o) (j : J a) → B .parts o m sp a ≡ g a j)
    → ((a : Σ .arity o) → (J a → ⊥) → A a (B .parts o m sp a))
    → Q m
    where open import Cubical.Data.Empty using (⊥)
