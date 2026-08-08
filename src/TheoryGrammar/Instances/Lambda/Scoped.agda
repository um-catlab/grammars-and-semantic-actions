{- Well-scoped terms, as the generic `μ`. No bespoke datatype: `Scoped` is
   `Ind.μ` at `ScopedF`, a description in the generic functor language,
   with the SCOPE as nonterminal index -- so the binder's action on the
   scope lives entirely in the index of the recursive occurrence. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Scoped where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit

open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base

module Wellscoped (Name : Type₀) where

  open LamBase Name

  Scope : Type₀
  Scope = List Name

  -- `In Γ n` DENOTES: "`n` occurs in the scope `Γ`".
  In : Scope → NmG
  In []      = ⊥G
  In (m ∷ Γ) = ⌈ m ⌉ ⊕ In Γ

  -- nonterminals: one per scope, all at sort `tm`
  open Ind λFib ℓ-zero Scope (λ _ → tm) public

  data ScTag : Type₀ where
    tVar tApp tLam : ScTag

  -- Three alternatives, one per operation. The binder: `⊕e Name` guesses
  -- the bound name, `⌜ ⌈ n ⌉ ⌝` pins the name slot to it, and the body's
  -- nonterminal is `n ∷ Γ`.
  ScopedF : Scope → Functor tm
  ScopedF Γ = ⊕e ScTag λ
    { tVar → ⊗e varOp (λ _ → ⌜ In Γ ⌝)
    ; tApp → ⊗e appOp (λ _ → Var Γ)
    ; tLam → ⊕e Name λ n → ⊗e lamOp (λ { true  → ⌜ ⌈ n ⌉ ⌝
                                       ; false → Var (n ∷ Γ) })
    }

  -- `Scoped Γ t` DENOTES: "`t` is a term all of whose free names occur
  -- in `Γ`" -- a scoping DERIVATION, not a yes/no.
  Scoped : Scope → TmG
  Scoped Γ t = μ ScopedF (Γ , t)

  -- `Step M Γ t` DENOTES: "`t` is scoped in `Γ` BY ONE RULE, with the
  -- immediate subterms taken from `M`" -- the three rules as a sum, so
  -- `Scoped` is its least fixed point.
  Step : (Scope → TmG) → Scope → TmG
  Step M Γ =   VarG (In Γ)
             ⊕ (AppG (M Γ) (M Γ)
             ⊕ ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (M (n ∷ Γ))))

  -- PRIMITIVE: the container encoding, respelled in the connectives
  ⟦Sc⟧ : {M : Ix → Type₀} (Γ : Scope)
       → ⟦ ScopedF Γ ⟧ M ⊢ Step (λ Δ x → M (Δ , x)) Γ
  ⟦Sc⟧ Γ _ ((tVar , sp , sh) , _) = inl (sp , λ a → lower (sh a))
  ⟦Sc⟧ Γ _ ((tApp , sp , _) , rc) =
    inr (inl (sp , λ { true → rc (true , tt*) ; false → rc (false , tt*) }))
  ⟦Sc⟧ Γ _ ((tLam , n , sp , sh) , rc) =
    inr (inr (n , sp , λ { true → lower (sh true) ; false → rc (false , tt*) }))

  ⟦Sc⟧⁻ : {M : Ix → Type₀} (Γ : Scope)
        → Step (λ Δ x → M (Δ , x)) Γ ⊢ ⟦ ScopedF Γ ⟧ M
  ⟦Sc⟧⁻ Γ _ (inl (sp , h)) =
    (tVar , sp , λ a → lift (h a)) , λ { (_ , ()) }
  ⟦Sc⟧⁻ Γ _ (inr (inl (sp , h))) =
    (tApp , sp , λ _ → tt*)
      , λ { (true , _) → h true ; (false , _) → h false }
  ⟦Sc⟧⁻ Γ _ (inr (inr (n , sp , h))) =
    (tLam , n , sp , λ { true → lift (h true) ; false → tt* })
      , λ { (true , ()) ; (false , _) → h false }

  -- from here down, nothing matches
  sc-unroll : (Γ : Scope) → Scoped Γ ⊢ Step Scoped Γ
  sc-unroll Γ = ⟦Sc⟧ Γ ∘g μ-coalg ScopedF Γ

  sc-roll : (Γ : Scope) → Step Scoped Γ ⊢ Scoped Γ
  sc-roll Γ = μ-alg ScopedF Γ ∘g ⟦Sc⟧⁻ Γ

  -- the three rules: `roll` after a coproduct injection
  sc-var : (Γ : Scope) → VarG (In Γ) ⊢ Scoped Γ
  sc-var Γ = sc-roll Γ ∘g ⊕-I₁

  sc-app : (Γ : Scope) → AppG (Scoped Γ) (Scoped Γ) ⊢ Scoped Γ
  sc-app Γ = sc-roll Γ ∘g (⊕-I₂ ∘g ⊕-I₁)

  sc-lam : (Γ : Scope) (n : Name) → LamG ⌈ n ⌉ (Scoped (n ∷ Γ)) ⊢ Scoped Γ
  sc-lam Γ n = sc-roll Γ ∘g (⊕-I₂ ∘g (⊕-I₂ ∘g ⊕ᴰ-I Name n))
