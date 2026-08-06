{-
  Syntax for free from a signature.

  Given a many-sorted signature, generate a formal system:
    * types      -- one ⊗ per operation, one ⊸ per (operation, slot)
    * contexts   -- signature-terms whose leaves are types, so linearity
                    is STRUCTURAL: there are no variable names to repeat
    * derivations -- a fixed set of rule shapes, quantified over ops
  and interpret it in grammars over any algebra for the signature.

  Nothing here is specific to strings or to lambda terms; both are
  instances of `Sig`.
-}
module Grammar.GenericSyntax where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base

private variable ℓ : Level

record Sig ℓ : Type (ℓ-suc ℓ) where
  field
    Sort    : Type ℓ
    Op      : Type ℓ
    arity   : Op → Type ℓ
    argSort : (o : Op) → arity o → Sort
    resSort : Op → Sort

open Sig

module Syntax {ℓ} (Σ : Sig ℓ)
  -- slot residuals need to distinguish the abstracted argument
  (arity? : (o : Σ .Op) → Discrete (Σ .arity o))
  (Atom : Σ .Sort → Type ℓ) where

  -- replace the i-th component of a family
  plug : (X : Σ .Sort → Type ℓ) (o : Σ .Op) (i : Σ .arity o)
    → X (Σ .argSort o i)
    → ((a : Σ .arity o) → X (Σ .argSort o a))
    → ((a : Σ .arity o) → X (Σ .argSort o a))
  plug X o i x f a with arity? o a i
  ... | yes p = subst (λ z → X (Σ .argSort o z)) (sym p) x
  ... | no  _ = f a

  -- ================================================================
  -- Types: one ⊗ per operation, one ⊸ per (operation, slot).
  -- ================================================================

  data Ty : Σ .Sort → Type ℓ where
    atom : ∀ {s} → Atom s → Ty s
    ⊗_∙_ : (o : Σ .Op)
         → ((a : Σ .arity o) → Ty (Σ .argSort o a))
         → Ty (Σ .resSort o)
    ⊸_,_∙_⇒_ : (o : Σ .Op) (i : Σ .arity o)
         → ((a : Σ .arity o) → Ty (Σ .argSort o a))   -- siblings; i-th ignored
         → Ty (Σ .resSort o)
         → Ty (Σ .argSort o i)

  -- ================================================================
  -- Contexts: signature-terms with types at the leaves.  Each leaf is
  -- one hypothesis, so linearity is structural -- no names, no
  -- occurrence counting, no partitioning of a variable list.
  -- ================================================================

  data Ctx : Σ .Sort → Type ℓ where
    ⟨_⟩  : ∀ {s} → Ty s → Ctx s
    node : (o : Σ .Op)
         → ((a : Σ .arity o) → Ctx (Σ .argSort o a))
         → Ctx (Σ .resSort o)

  -- ================================================================
  -- Derivations.  Natural deduction: intro and elim per connective.
  -- ================================================================

  data _⊢_ : ∀ {s} → Ctx s → Ty s → Type ℓ where

    id : ∀ {s} {A : Ty s} → ⟨ A ⟩ ⊢ A

    ⊗I : (o : Σ .Op)
       {Γ : (a : Σ .arity o) → Ctx (Σ .argSort o a)}
       {A : (a : Σ .arity o) → Ty (Σ .argSort o a)}
       → (∀ a → Γ a ⊢ A a)
       → node o Γ ⊢ (⊗ o ∙ A)

    ⊸I : (o : Σ .Op) (i : Σ .arity o)
       {A : (a : Σ .arity o) → Ty (Σ .argSort o a)}
       {B : Ty (Σ .resSort o)}
       {Γ : Ctx (Σ .argSort o i)}
       → node o (plug Ctx o i Γ (λ a → ⟨ A a ⟩)) ⊢ B
       → Γ ⊢ (⊸ o , i ∙ A ⇒ B)

    ⊸E : (o : Σ .Op) (i : Σ .arity o)
       {A : (a : Σ .arity o) → Ty (Σ .argSort o a)}
       {B : Ty (Σ .resSort o)}
       {Γ : Ctx (Σ .argSort o i)}
       {Δ : (a : Σ .arity o) → Ctx (Σ .argSort o a)}
       → Γ ⊢ (⊸ o , i ∙ A ⇒ B)
       → (∀ a → Δ a ⊢ A a)
       → node o (plug Ctx o i Γ Δ) ⊢ B

-- ==================================================================
-- Semantics: grammars over any algebra, with the splitting relation
-- as a parameter (the promonoidal presentation).
-- ==================================================================

record Base {ℓ} (Σ : Sig ℓ) : Type (ℓ-suc ℓ) where
  field
    carrier : Σ .Sort → Type ℓ
    Split   : (o : Σ .Op)
            → ((a : Σ .arity o) → carrier (Σ .argSort o a))
            → carrier (Σ .resSort o) → Type ℓ

open Base

module Semantics {ℓ} (Σ : Sig ℓ)
  (arity? : (o : Σ .Op) → Discrete (Σ .arity o))
  (Atom : Σ .Sort → Type ℓ)
  (B : Base Σ)
  (⟦atom⟧ : ∀ {s} → Atom s → B .carrier s → Type ℓ) where

  open Syntax Σ arity? Atom

  Gr : Σ .Sort → Type (ℓ-suc ℓ)
  Gr s = B .carrier s → Type ℓ

  _⊨_ : ∀ {s} → Gr s → Gr s → Type ℓ
  P ⊨ Q = ∀ m → P m → Q m

  ⊗G : (o : Σ .Op) → ((a : Σ .arity o) → Gr (Σ .argSort o a)) → Gr (Σ .resSort o)
  ⊗G o P m =
    Σ[ m⃗ ∈ ((a : Σ .arity o) → B .carrier (Σ .argSort o a)) ]
      (B .Split o m⃗ m × ((a : Σ .arity o) → P a (m⃗ a)))

  ⊸G : (o : Σ .Op) (i : Σ .arity o)
     → ((a : Σ .arity o) → Gr (Σ .argSort o a))
     → Gr (Σ .resSort o) → Gr (Σ .argSort o i)
  ⊸G o i P Q x =
    (m⃗ : (a : Σ .arity o) → B .carrier (Σ .argSort o a))
    (m : B .carrier (Σ .resSort o))
    → B .Split o (plug (B .carrier) o i x m⃗) m
    → ((a : Σ .arity o) → ¬ (a ≡ i) → P a (m⃗ a))
    → Q m

  ⟦_⟧T : ∀ {s} → Ty s → Gr s
  ⟦ atom x ⟧T          = ⟦atom⟧ x
  ⟦ ⊗ o ∙ A ⟧T         = ⊗G o (λ a → ⟦ A a ⟧T)
  ⟦ ⊸ o , i ∙ A ⇒ C ⟧T = ⊸G o i (λ a → ⟦ A a ⟧T) ⟦ C ⟧T

  ⟦_⟧C : ∀ {s} → Ctx s → Gr s
  ⟦ ⟨ A ⟩ ⟧C     = ⟦ A ⟧T
  ⟦ node o Γ ⟧C  = ⊗G o (λ a → ⟦ Γ a ⟧C)

  -- soundness: every derivation denotes a grammar morphism
  ⟦_⟧D : ∀ {s} {Γ : Ctx s} {A : Ty s} → Γ ⊢ A → ⟦ Γ ⟧C ⊨ ⟦ A ⟧T
  -- plugging the i-th component back is the identity.  The transport
  -- below exists only because `arity?` is a parameter: at any concrete
  -- signature `arity? o a i` reduces and `plug` computes away.
  plug-id : (o : Σ .Op) (i : Σ .arity o)
    (n⃗ : (a : Σ .arity o) → B .carrier (Σ .argSort o a))
    → ∀ a → plug (B .carrier) o i (n⃗ i) n⃗ a ≡ n⃗ a
  plug-id o i n⃗ a with arity? o a i
  ... | no ¬p = refl
  ... | yes p =
    J (λ y q → subst (λ z → B .carrier (Σ .argSort o z)) (sym q) (n⃗ y) ≡ n⃗ a)
      (substRefl {B = λ z → B .carrier (Σ .argSort o z)} (n⃗ a)) p

  ⟦ id ⟧D m x = x
  ⟦ ⊗I o d ⟧D m (m⃗ , sp , g) = m⃗ , sp , λ a → ⟦ d a ⟧D (m⃗ a) (g a)
  ⟦ ⊸I o i d ⟧D = {!   !}
  ⟦ ⊸E o i d e ⟧D = {!   !}
