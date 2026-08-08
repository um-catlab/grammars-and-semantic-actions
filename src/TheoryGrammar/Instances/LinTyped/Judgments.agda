{- THE BIDIRECTIONAL LINEAR JUDGMENTS, as ONE `μ` with TWO nonterminals. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Judgments where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt; tt*)

open import TheoryGrammar.Base
open import TheoryGrammar.Distributive
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered
open import TheoryGrammar.Instances.LinTyped.Base
open import TheoryGrammar.Instances.LinTyped.Context

-- `Mode` denotes the direction a judgment is read in: `syn` produces
-- its type, `chk` consumes it.
data Mode : Type₀ where
  syn chk : Mode

-- `NT` denotes a nonterminal: a mode, the context it is under, and the
-- type it produces or consumes.
NT : Type₀
NT = Mode × Ctx × Ty

-- both nonterminals live at sort `tm`
open Ind linFib ℓ-zero NT (λ _ → tm) public

-- `InfTag`/`ChkTag` denote which RULE was used.
data InfTag : Type₀ where
  tVar tApp tAnn : InfTag

data ChkTag : Type₀ where
  tSwitch tLam : ChkTag

-- domain and codomain, read off a `ty`-splitting by `parts`.  There is
-- no `Ty → Maybe Ty`: the CALLER holds an `IsLol` witness.
dom cod : {C : Ty} → IsLol C → Ty
dom {C} sp = TParts lolOp C sp true
cod {C} sp = TParts lolOp C sp false

-- `JF x` denotes the one-step rule set at nonterminal `x`.
JF : (x : NT) → Functor tm
JF (syn , Γ , A) = ⊕e InfTag λ
  { tVar → ⊗e varOp (λ _ → ⌜ Solo Γ A ⌝)
  ; tApp → ⊕e (SplitΣ Γ) λ z → ⊕e Ty λ A₀ →
             ⊗e appOp (λ { true  → Var (syn , z .fst , A₀ ⊸ᵗ A)
                         ; false → Var (chk , z .snd .fst , A₀) })
  ; tAnn → ⊗e annOp (λ { true  → Var (chk , Γ , A)
                       ; false → ⌜ ⌈_⌉ {s = ty} A ⌝ })
  }
JF (chk , Γ , C) = ⊕e ChkTag λ
  { tSwitch → Var (syn , Γ , C)
  ; tLam → ⊕e (IsLol C) λ sa →
             ⊗e lamOp (λ _ → Var (chk , just (dom sa) ∷ Γ , cod sa))
  }

-- `Jμ x` denotes the derivations at nonterminal `x`.
Jμ : NT → TmG
Jμ x t = μ JF (x , t)

-- `Infer Γ A` denotes "this term SYNTHESISES `A` in `Γ`"; `Check Γ C`
-- denotes "this term CHECKS against `C` in `Γ`".  In both, "in `Γ`"
-- means it uses EVERY slot `Γ` owns, exactly once.
Infer Check : Ctx → Ty → TmG
Infer Γ A = Jμ (syn , Γ , A)
Check Γ C = Jμ (chk , Γ , C)

-- `Syn Γ` denotes "this term synthesises SOME type in `Γ`", with the
-- type carried as the sum's index.
Syn : Ctx → TmG
Syn Γ = ⊕ᴰ Ty (Infer Γ)

-- One unfolding, in the connectives.

JStep : (NT → TmG) → NT → TmG
JStep R (syn , Γ , A) =
    VarG (Solo Γ A)
  ⊕ ( SplitG Γ (λ Γ₁ Γ₂ →
        ⊕ᴰ Ty (λ A₀ → AppG (R (syn , Γ₁ , A₀ ⊸ᵗ A)) (R (chk , Γ₂ , A₀))))
    ⊕ AnnG (R (chk , Γ , A)) (⌈_⌉ {s = ty} A))
JStep R (chk , Γ , C) =
    R (syn , Γ , C)
  ⊕ ⊕ᴰ (IsLol C) (λ sa → LamG (R (chk , just (dom sa) ∷ Γ , cod sa)))

-- PRIMITIVE: the two respellings -- "read a container layer as a layer
-- of connectives" and its converse.
⟦J⟧ : {M : Ix → Type₀} (x : NT) → ⟦ JF x ⟧ M ⊢ JStep (λ y t → M (y , t)) x
⟦J⟧ (syn , Γ , A) _ ((tVar , sp , sh) , _) = inl (sp , λ a → lower (sh a))
⟦J⟧ (syn , Γ , A) _ ((tApp , z , A₀ , sp , _) , rc) =
  inr (inl (z , A₀ , sp
           , λ { true → rc (true , tt*) ; false → rc (false , tt*) }))
⟦J⟧ (syn , Γ , A) _ ((tAnn , sp , sh) , rc) =
  inr (inr (sp , λ { true → rc (true , tt*) ; false → lower (sh false) }))
⟦J⟧ (chk , Γ , C) _ ((tSwitch , _) , rc) = inl (rc tt*)
⟦J⟧ (chk , Γ , C) _ ((tLam , sa , sp , _) , rc) =
  inr (sa , sp , λ _ → rc (tt , tt*))

⟦J⟧⁻ : {M : Ix → Type₀} (x : NT) → JStep (λ y t → M (y , t)) x ⊢ ⟦ JF x ⟧ M
⟦J⟧⁻ (syn , Γ , A) _ (inl (sp , h)) =
  (tVar , sp , λ a → lift (h a)) , λ { (_ , ()) }
⟦J⟧⁻ (syn , Γ , A) _ (inr (inl (z , A₀ , sp , h))) =
  (tApp , z , A₀ , sp , λ { true → tt* ; false → tt* })
    , λ { (true , _) → h true ; (false , _) → h false }
⟦J⟧⁻ (syn , Γ , A) _ (inr (inr (sp , h))) =
  (tAnn , sp , λ { true → tt* ; false → lift (h false) })
    , λ { (true , _) → h true ; (false , ()) }
⟦J⟧⁻ (chk , Γ , C) _ (inl d) = (tSwitch , tt*) , λ _ → d
⟦J⟧⁻ (chk , Γ , C) _ (inr (sa , sp , h)) =
  (tLam , sa , sp , λ _ → tt*) , λ _ → h tt

-- from here down, nothing matches
j-unroll : (x : NT) → Jμ x ⊢ JStep Jμ x
j-unroll x = ⟦J⟧ x ∘g μ-coalg JF x

j-roll : (x : NT) → JStep Jμ x ⊢ Jμ x
j-roll x = μ-alg JF x ∘g ⟦J⟧⁻ x

-- The five rules: `roll` after a coproduct injection.

inf-var : (Γ : Ctx) (A : Ty) → VarG (Solo Γ A) ⊢ Infer Γ A
inf-var Γ A = j-roll (syn , Γ , A) ∘g ⊕-I₁

-- THE LINEAR APPLICATION RULE.  Note the premises sit at `Γ₁` and `Γ₂`,
-- and the splitting `s` is DATA that the derivation carries.
inf-app : (Γ Γ₁ Γ₂ : Ctx) (s : Γ₁ ⊎ᶜ Γ₂ ↝ Γ) (A₀ A : Ty)
        → AppG (Infer Γ₁ (A₀ ⊸ᵗ A)) (Check Γ₂ A₀) ⊢ Infer Γ A
inf-app Γ Γ₁ Γ₂ s A₀ A =
  j-roll (syn , Γ , A)
  ∘g (⊕-I₂ ∘g (⊕-I₁
       ∘g ⊕ᴰ-I (SplitΣ Γ)
            {A = λ z → ⊕ᴰ Ty (λ B₀ →
                   AppG (Infer (z .fst) (B₀ ⊸ᵗ A)) (Check (z .snd .fst) B₀))}
            (Γ₁ , Γ₂ , s)
       ∘g ⊕ᴰ-I Ty
            {A = λ B₀ → AppG (Infer Γ₁ (B₀ ⊸ᵗ A)) (Check Γ₂ B₀)} A₀))

inf-ann : (Γ : Ctx) (A : Ty)
        → AnnG (Check Γ A) (⌈_⌉ {s = ty} A) ⊢ Infer Γ A
inf-ann Γ A = j-roll (syn , Γ , A) ∘g (⊕-I₂ ∘g ⊕-I₂)

chk-switch : (Γ : Ctx) (C : Ty) → Infer Γ C ⊢ Check Γ C
chk-switch Γ C = j-roll (chk , Γ , C) ∘g ⊕-I₁

chk-lam : (Γ : Ctx) (C : Ty) (sa : IsLol C)
        → LamG (Check (just (dom sa) ∷ Γ) (cod sa)) ⊢ Check Γ C
chk-lam Γ C sa =
  j-roll (chk , Γ , C)
  ∘g (⊕-I₂ ∘g ⊕ᴰ-I (IsLol C)
        {A = λ sa' → LamG (Check (just (dom sa') ∷ Γ) (cod sa'))} sa)

-- THE SAME UNFOLDING FOR `Syn Γ`, with the ⊕ᴰ pushed inwards.

QVar : Ctx → Ty → TmG
QVar Γ A = VarG (Solo Γ A)

-- the application rule at a FIXED synthesised type, splittings still
-- guessed
QApp' : Ctx → Ty → TmG
QApp' Γ A =
  SplitG Γ (λ Γ₁ Γ₂ →
    ⊕ᴰ Ty (λ A₀ → AppG (Infer Γ₁ (A₀ ⊸ᵗ A)) (Check Γ₂ A₀)))

-- ... and with BOTH types named at once, so one `⊕ᴰ` guesses the pair
QApp : Ctx → Ctx → Ty × Ty → TmG
QApp Γ₁ Γ₂ AB = AppG (Infer Γ₁ (AB .fst ⊸ᵗ AB .snd)) (Check Γ₂ (AB .fst))

SynApp : Ctx → TmG
SynApp Γ = SplitG Γ (λ Γ₁ Γ₂ → ⊕ᴰ (Ty × Ty) (QApp Γ₁ Γ₂))

QAnn : Ctx → Ty → TmG
QAnn Γ A = AnnG (Check Γ A) (⌈_⌉ {s = ty} A)

SynAnn : Ctx → TmG
SynAnn Γ = ⊕ᴰ Ty (QAnn Γ)

-- `SynStep Γ` denotes one layer of `Syn Γ`.
SynStep : Ctx → TmG
SynStep Γ = VarG (Look Γ) ⊕ (SynApp Γ ⊕ SynAnn Γ)

-- internal: the ⊕ᴰ goes INTO the unary tensor by its functorial action
varG-push : (Γ : Ctx) → ⊕ᴰ Ty (QVar Γ) ⊢ VarG (Look Γ)
varG-push Γ = ⊕ᴰ-E λ A →
  ⊗ˢ-map varOp {A = varFam (Solo Γ A)} {B = varFam (Look Γ)}
         (λ _ → ⊕ᴰ-I Ty {A = Solo Γ} A)

-- PRIMITIVE: and out again.  This direction is NOT internal -- it reads
-- the index out of a slot and republishes it at the whole -- but for a
-- UNARY operation it is only `Unit`'s η.
varG-pull : (Γ : Ctx) → VarG (Look Γ) ⊢ ⊕ᴰ Ty (QVar Γ)
varG-pull Γ t (sp , h) = h tt .fst , sp , λ _ → h tt .snd

-- internal: reindexing iterated ⊕ᴰs
appReindex : (Γ : Ctx) → ⊕ᴰ Ty (QApp' Γ) ⊢ SynApp Γ
appReindex Γ = ⊕ᴰ-E λ A → ⊕ᴰ-E λ z → ⊕ᴰ-E λ A₀ →
    ⊕ᴰ-I (SplitΣ Γ)
      {A = λ z' → ⊕ᴰ (Ty × Ty) (QApp (z' .fst) (z' .snd .fst))} z
  ∘g ⊕ᴰ-I (Ty × Ty) {A = QApp (z .fst) (z .snd .fst)} (A₀ , A)

appReindex⁻ : (Γ : Ctx) → SynApp Γ ⊢ ⊕ᴰ Ty (QApp' Γ)
appReindex⁻ Γ = ⊕ᴰ-E λ z → ⊕ᴰ-E λ AB →
    ⊕ᴰ-I Ty {A = QApp' Γ} (AB .snd)
  ∘g ⊕ᴰ-I (SplitΣ Γ)
       {A = λ z' → ⊕ᴰ Ty (λ A₀ →
              AppG (Infer (z' .fst) (A₀ ⊸ᵗ AB .snd))
                   (Check (z' .snd .fst) A₀))} z
  ∘g ⊕ᴰ-I Ty
       {A = λ A₀ → AppG (Infer (z .fst) (A₀ ⊸ᵗ AB .snd))
                        (Check (z .snd .fst) A₀)} (AB .fst)

syn-out : (Γ : Ctx) → Syn Γ ⊢ SynStep Γ
syn-out Γ =
    ⊕-E (⊕-I₁ ∘g varG-push Γ)
        (⊕-I₂ ∘g (⊕-E (⊕-I₁ ∘g appReindex Γ) ⊕-I₂ ∘g ⊕ᴰ-⊕-out Ty))
  ∘g (⊕ᴰ-⊕-out Ty ∘g ⊕ᴰ-map Ty (λ A → j-unroll (syn , Γ , A)))

syn-in : (Γ : Ctx) → SynStep Γ ⊢ Syn Γ
syn-in Γ =
    ⊕ᴰ-map Ty (λ A → j-roll (syn , Γ , A))
  ∘g (⊕ᴰ-⊕-in Ty
      ∘g ⊕-E (⊕-I₁ ∘g varG-pull Γ)
             (⊕-I₂ ∘g (⊕ᴰ-⊕-in Ty
                       ∘g ⊕-E (⊕-I₁ ∘g appReindex⁻ Γ) ⊕-I₂)))
