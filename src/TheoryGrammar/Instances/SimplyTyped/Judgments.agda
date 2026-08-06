{-
  THE BIDIRECTIONAL JUDGMENTS, as ONE `μ` with TWO nonterminals.

  The nonterminal index is `Mode × Ctx × Ty`, all at sort `tm`; so
  `Infer Γ A` and `Check Γ C` are two families of the same fixed point
  and the mode discipline is a property of the DESCRIPTION, not of a
  separate datatype:

    Infer  var    the name is bound in Γ, to the index type
           app    the function's type is A₀ ⇒ A for some GUESSED A₀,
                  whose argument is CHECKED
           ann    the term is checked at the type sitting in the ty slot,
                  which the representable `⌈ A ⌉` pins to the index
    Check  switch synthesis at the very same type
           lam    only when the index type SPLITS as an arrow -- and the
                  splitting comes from the substrate at sort `ty`, so no
                  case analysis on `Ty` appears in the description

  That last point is what the third sort buys: `⊕e (IsArr C)` is the
  substrate's own `Split arrOp C`, so the lambda rule is present exactly
  when the checking type is an arrow, with `dom`/`cod` read off by
  `parts` rather than by matching.

  PRIMITIVE: `⟦J⟧`/`⟦J⟧⁻`, the container encoding respelled in the
  connectives.  They never match a term and never open a splitting.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Judgments where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Substrate
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Readable
open import TheoryGrammar.Instances.SimplyTyped.Types
open import TheoryGrammar.Instances.SimplyTyped.Context

module Judgments (Name : Type₀) (_≟_ : Discrete Name) where

  open StBase Name
  open StReadable Name
  open StTypes Name
  open StContext Name _≟_

  data Mode : Type₀ where
    syn chk : Mode

  NT : Type₀
  NT = Mode × Ctx × Ty

  -- both nonterminals live at sort `tm`
  open Ind stlcSub ℓ-zero NT (λ _ → tm) public

  data InfTag : Type₀ where
    tVar tApp tAnn : InfTag

  data ChkTag : Type₀ where
    tSwitch tLam : ChkTag

  -- domain and codomain, read off a `ty`-splitting by `parts`
  dom cod : {C : Ty} → IsArr C → Ty
  dom {C} sp = TParts arrOp C sp true
  cod {C} sp = TParts arrOp C sp false

  JF : (x : NT) → Functor tm
  JF (syn , Γ , A) = ⊕e InfTag λ
    { tVar → ⊗e varOp (λ _ → ⌜ Lookup Γ A ⌝)
    ; tApp → ⊕e Ty λ A₀ →
               ⊗e appOp (λ { true  → Var (syn , Γ , A₀ ⇒ᵗ A)
                           ; false → Var (chk , Γ , A₀) })
    ; tAnn → ⊗e annOp (λ { true  → Var (chk , Γ , A)
                         ; false → ⌜ ⌈_⌉ {s = ty} A ⌝ })
    }
  JF (chk , Γ , C) = ⊕e ChkTag λ
    { tSwitch → Var (syn , Γ , C)
    ; tLam → ⊕e (IsArr C) λ sa → ⊕e Name λ n →
               ⊗e lamOp (λ { true  → ⌜ Nm n ⌝
                           ; false → Var (chk , (n , dom sa) ∷ Γ , cod sa) })
    }

  Jμ : NT → TmG
  Jμ x t = μ JF (x , t)

  Infer Check : Ctx → Ty → TmG
  Infer Γ A = Jμ (syn , Γ , A)
  Check Γ C = Jμ (chk , Γ , C)

  -- the synthesis grammar: the indexed sum whose subsingleton-ness is
  -- the whole question
  Syn : Ctx → TmG
  Syn Γ = ⊕ᴰ Ty (Infer Γ)

  -- ================================================================
  -- One unfolding, in the connectives.
  -- ================================================================

  JStep : (NT → TmG) → NT → TmG
  JStep R (syn , Γ , A) =
      VarG (Lookup Γ A)
    ⊕ (⊕ᴰ Ty (λ A₀ → AppG (R (syn , Γ , A₀ ⇒ᵗ A)) (R (chk , Γ , A₀)))
    ⊕ AnnG (R (chk , Γ , A)) (⌈_⌉ {s = ty} A))
  JStep R (chk , Γ , C) =
      R (syn , Γ , C)
    ⊕ ⊕ᴰ (IsArr C) (λ sa → ⊕ᴰ Name (λ n →
        LamG (Nm n) (R (chk , (n , dom sa) ∷ Γ , cod sa))))

  -- PRIMITIVE: the container encoding, respelled in the connectives
  ⟦J⟧ : {M : Ix → Type₀} (x : NT) → ⟦ JF x ⟧ M ⊢ JStep (λ y t → M (y , t)) x
  ⟦J⟧ (syn , Γ , A) _ ((tVar , sp , sh) , _) = inl (sp , λ a → lower (sh a))
  ⟦J⟧ (syn , Γ , A) _ ((tApp , A₀ , sp , _) , rc) =
    inr (inl (A₀ , sp , λ { true → rc (true , tt*) ; false → rc (false , tt*) }))
  ⟦J⟧ (syn , Γ , A) _ ((tAnn , sp , sh) , rc) =
    inr (inr (sp , λ { true → rc (true , tt*) ; false → lower (sh false) }))
  ⟦J⟧ (chk , Γ , C) _ ((tSwitch , _) , rc) = inl (rc tt*)
  ⟦J⟧ (chk , Γ , C) _ ((tLam , sa , n , sp , sh) , rc) =
    inr (sa , n , sp , λ { true → lower (sh true) ; false → rc (false , tt*) })

  ⟦J⟧⁻ : {M : Ix → Type₀} (x : NT) → JStep (λ y t → M (y , t)) x ⊢ ⟦ JF x ⟧ M
  ⟦J⟧⁻ (syn , Γ , A) _ (inl (sp , h)) =
    (tVar , sp , λ a → lift (h a)) , λ { (_ , ()) }
  ⟦J⟧⁻ (syn , Γ , A) _ (inr (inl (A₀ , sp , h))) =
    (tApp , A₀ , sp , λ { true → tt* ; false → tt* })
      , λ { (true , _) → h true ; (false , _) → h false }
  ⟦J⟧⁻ (syn , Γ , A) _ (inr (inr (sp , h))) =
    (tAnn , sp , λ { true → tt* ; false → lift (h false) })
      , λ { (true , _) → h true ; (false , ()) }
  ⟦J⟧⁻ (chk , Γ , C) _ (inl d) = (tSwitch , tt*) , λ _ → d
  ⟦J⟧⁻ (chk , Γ , C) _ (inr (sa , n , sp , h)) =
    (tLam , sa , n , sp , λ { true → lift (h true) ; false → tt* })
      , λ { (true , ()) ; (false , _) → h false }

  -- from here down, nothing matches
  j-unroll : (x : NT) → Jμ x ⊢ JStep Jμ x
  j-unroll x = ⟦J⟧ x ∘g μ-coalg JF x

  j-roll : (x : NT) → JStep Jμ x ⊢ Jμ x
  j-roll x = μ-alg JF x ∘g ⟦J⟧⁻ x

  -- ================================================================
  -- The five rules: `roll` after a coproduct injection.
  -- ================================================================

  inf-var : (Γ : Ctx) (A : Ty) → VarG (Lookup Γ A) ⊢ Infer Γ A
  inf-var Γ A = j-roll (syn , Γ , A) ∘g ⊕-I₁

  inf-app : (Γ : Ctx) (A₀ A : Ty)
          → AppG (Infer Γ (A₀ ⇒ᵗ A)) (Check Γ A₀) ⊢ Infer Γ A
  inf-app Γ A₀ A =
    j-roll (syn , Γ , A)
    ∘g (⊕-I₂ ∘g (⊕-I₁ ∘g ⊕ᴰ-I Ty
          {A = λ A₁ → AppG (Infer Γ (A₁ ⇒ᵗ A)) (Check Γ A₁)} A₀))

  inf-ann : (Γ : Ctx) (A : Ty)
          → AnnG (Check Γ A) (⌈_⌉ {s = ty} A) ⊢ Infer Γ A
  inf-ann Γ A = j-roll (syn , Γ , A) ∘g (⊕-I₂ ∘g ⊕-I₂)

  chk-switch : (Γ : Ctx) (C : Ty) → Infer Γ C ⊢ Check Γ C
  chk-switch Γ C = j-roll (chk , Γ , C) ∘g ⊕-I₁

  chk-lam : (Γ : Ctx) (C : Ty) (sa : IsArr C) (n : Name)
          → LamG (Nm n) (Check ((n , dom sa) ∷ Γ) (cod sa)) ⊢ Check Γ C
  chk-lam Γ C sa n =
    j-roll (chk , Γ , C)
    ∘g (⊕-I₂ ∘g (⊕ᴰ-I (IsArr C)
          {A = λ sa' → ⊕ᴰ Name (λ n' →
                 LamG (Nm n') (Check ((n' , dom sa') ∷ Γ) (cod sa')))} sa
        ∘g ⊕ᴰ-I Name
          {A = λ n' → LamG (Nm n') (Check ((n' , dom sa) ∷ Γ) (cod sa))} n))
