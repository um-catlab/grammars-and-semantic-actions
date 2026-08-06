{-
  THE BIDIRECTIONAL TYPECHECKER, as one map of the calculus:

      typecheck : ⊤ ⊢   &ᴰ Ctx      (λ Γ     → Dec⟨ Syn Γ ⟩)
                      & &ᴰ (Ctx×Ty) (λ (Γ,C) → Dec⟨ Check Γ C ⟩)

  Both modes are decided at once, for every context (and every checking
  type), because the context grows while the term shrinks -- exactly as
  in the scope checker.

  The load-bearing lemma is `dec-at`:

      dec-at : ((A B : Ty) → (Infer Γ A & Infer Γ B) ⊢ Kty A B)
             → Dec⟨ Syn Γ ⟩ ⊢ Dec⟨ Infer Γ C ⟩

  Deciding synthesis gives deciding checking-at-a-type ONLY GIVEN the
  subsingleton hypothesis, which is stated as an explicit argument so
  the dependency is a theorem and not a remark.  The same hypothesis is
  what lets the application case REFUTE: if the function synthesises a
  non-arrow, or an arrow whose domain the argument fails, there is no
  other type it could have synthesised.

  `dec-appᵈ` is the only decision written by hand; `⊗-decSplit`,
  `dec-⊗`, `dec-⊕`, `dec-map` and the two `Dependent` decisions do
  everything else.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Check where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Empty as E using ()
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Substrate
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Grading
open import TheoryGrammar.Instances.SimplyTyped.Readable
open import TheoryGrammar.Instances.SimplyTyped.Types
open import TheoryGrammar.Instances.SimplyTyped.Context
open import TheoryGrammar.Instances.SimplyTyped.Dependent
open import TheoryGrammar.Instances.SimplyTyped.Judgments
open import TheoryGrammar.Instances.SimplyTyped.Unique

module StCheck (Name : Type₀) (_≟_ : Discrete Name) where

  open StBase Name
  open Grading Name
  open StReadable Name
  open StTypes Name
  open StContext Name _≟_
  open StDependent Name
  open Judgments Name _≟_
  open StUnique Name _≟_

  -- ================================================================
  -- One unfolding of `Syn Γ`, with the ⊕ᴰ pushed inwards.
  -- ================================================================

  QVar : Ctx → Ty → TmG
  QVar Γ A = VarG (Lookup Γ A)

  QApp' : Ctx → Ty → TmG
  QApp' Γ A = ⊕ᴰ Ty (λ A₀ → AppG (Infer Γ (A₀ ⇒ᵗ A)) (Check Γ A₀))

  QAnn : Ctx → Ty → TmG
  QAnn Γ A = AnnG (Check Γ A) (⌈_⌉ {s = ty} A)

  QApp : Ctx → Ty × Ty → TmG
  QApp Γ AB = AppG (Infer Γ (AB .fst ⇒ᵗ AB .snd)) (Check Γ (AB .fst))

  SynApp : Ctx → TmG
  SynApp Γ = ⊕ᴰ (Ty × Ty) (QApp Γ)

  SynAnn : Ctx → TmG
  SynAnn Γ = ⊕ᴰ Ty (QAnn Γ)

  SynStep : Ctx → TmG
  SynStep Γ = VarG (Look Γ) ⊕ (SynApp Γ ⊕ SynAnn Γ)

  -- internal: the ⊕ᴰ goes INTO the unary tensor by its functorial action
  varG-push : (Γ : Ctx) → ⊕ᴰ Ty (QVar Γ) ⊢ VarG (Look Γ)
  varG-push Γ = ⊕ᴰ-E λ A →
    ⊗ˢ-map varOp {A = varFam (Lookup Γ A)} {B = varFam (Look Γ)}
           (λ _ → ⊕ᴰ-I Ty {A = Lookup Γ} A)

  -- PRIMITIVE: and out again.  This direction is NOT internal -- it
  -- reads the index out of a slot and republishes it at the whole --
  -- but for a UNARY operation it is only `Unit`'s η.
  varG-pull : (Γ : Ctx) → VarG (Look Γ) ⊢ ⊕ᴰ Ty (QVar Γ)
  varG-pull Γ t (sp , h) = h tt .fst , sp , λ _ → h tt .snd

  -- internal: reindexing an iterated ⊕ᴰ along a product
  appReindex : (Γ : Ctx) → ⊕ᴰ Ty (QApp' Γ) ⊢ SynApp Γ
  appReindex Γ = ⊕ᴰ-E λ A → ⊕ᴰ-E λ A₀ → ⊕ᴰ-I (Ty × Ty) {A = QApp Γ} (A₀ , A)

  appReindex⁻ : (Γ : Ctx) → SynApp Γ ⊢ ⊕ᴰ Ty (QApp' Γ)
  appReindex⁻ Γ = ⊕ᴰ-E λ AB →
      ⊕ᴰ-I Ty {A = QApp' Γ} (AB .snd)
    ∘g ⊕ᴰ-I Ty {A = λ A₀ → AppG (Infer Γ (A₀ ⇒ᵗ AB .snd)) (Check Γ A₀)} (AB .fst)

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

  -- ================================================================
  -- The application's dependent tensor: the argument's checking type
  -- comes from the FUNCTION's slot, and there is no representable
  -- pinning it, so this is where uniqueness has to be used.
  -- ================================================================

  AppGᵈ : Ctx → TmG
  AppGᵈ Γ t =
    Σ[ sp ∈ IsApp t ] Σ[ AB ∈ Ty × Ty ]
      ( Infer Γ (AB .fst ⇒ᵗ AB .snd) (TParts appOp t sp true)
      × Check Γ (AB .fst) (TParts appOp t sp false) )

  app-collapse : (Γ : Ctx) → SynApp Γ ⊢ AppGᵈ Γ
  app-collapse Γ t (AB , sp , h) = sp , AB , h true , h false

  app-collapse⁻ : (Γ : Ctx) → AppGᵈ Γ ⊢ SynApp Γ
  app-collapse⁻ Γ t (sp , AB , d , c) = AB , sp , λ { true → d ; false → c }

  module _ (Γ : Ctx) (t : Raw) where

    private
      Payload : IsApp t → Type₀
      Payload sp =
        Σ[ AB ∈ Ty × Ty ]
          ( Infer Γ (AB .fst ⇒ᵗ AB .snd) (TParts appOp t sp true)
          × Check Γ (AB .fst) (TParts appOp t sp false) )

      -- any witness splits the same way, by unique readability
      align : (sp : IsApp t) → AppGᵈ Γ t → Payload sp
      align sp y = subst Payload (Split-isProp appOp t (y .fst) sp) (y .snd)

    dec-appᵈ : ((sp : IsApp t) → Dec⟨ Syn Γ ⟩ (TParts appOp t sp true))
             → ((sp : IsApp t) (A₀ : Ty)
                → Dec⟨ Check Γ A₀ ⟩ (TParts appOp t sp false))
             → Dec⟨ AppGᵈ Γ ⟩ t
    dec-appᵈ dFn dArg with ⊗-decSplit appOp t tt
    ... | inr k = dec-no (AppGᵈ Γ) t λ y → k (y .fst , λ _ → tt)
    ... | inl x = fromFn (x .fst) (dFn (x .fst))
      where
      -- the function's type is an arrow, and the argument checks at its
      -- domain: the only positive case
      atArrow : (sp : IsApp t) (A₁ B₁ : Ty)
              → Infer Γ (A₁ ⇒ᵗ B₁) (TParts appOp t sp true)
              → Dec⟨ Check Γ A₁ ⟩ (TParts appOp t sp false)
              → Dec⟨ AppGᵈ Γ ⟩ t
      atArrow sp A₁ B₁ d (inl c) = dec-yes (AppGᵈ Γ) t (sp , (A₁ , B₁) , d , c)
      atArrow sp A₁ B₁ d (inr k) = dec-no (AppGᵈ Γ) t λ y →
        k (subst (λ X → Check Γ X (TParts appOp t sp false))
                 (sym (⇒ᵗ-inj A₁ B₁ (align sp y .fst .fst) (align sp y .fst .snd)
                        (synUnique Γ (A₁ ⇒ᵗ B₁)
                                   (align sp y .fst .fst ⇒ᵗ align sp y .fst .snd)
                                   (TParts appOp t sp true)
                                   (d , align sp y .snd .fst)) .fst))
                 (align sp y .snd .snd))

      -- SUBSINGLETON AT WORK: the synthesised type is the only one, so
      -- "it is not an arrow" really does refute the application
      atType : (sp : IsApp t) (C : Ty)
             → Infer Γ C (TParts appOp t sp true) → Dec⟨ AppGᵈ Γ ⟩ t
      atType sp base d = dec-no (AppGᵈ Γ) t λ y →
        E.rec (base≢arr (align sp y .fst .fst) (align sp y .fst .snd)
                (synUnique Γ base
                           (align sp y .fst .fst ⇒ᵗ align sp y .fst .snd)
                           (TParts appOp t sp true)
                           (d , align sp y .snd .fst)))
      atType sp (A₁ ⇒ᵗ B₁) d = atArrow sp A₁ B₁ d (dArg sp A₁)

      fromFn : (sp : IsApp t) → Dec⟨ Syn Γ ⟩ (TParts appOp t sp true)
             → Dec⟨ AppGᵈ Γ ⟩ t
      fromFn sp (inl (C , d)) = atType sp C d
      fromFn sp (inr k) = dec-no (AppGᵈ Γ) t λ y →
        k ( align sp y .fst .fst ⇒ᵗ align sp y .fst .snd
          , align sp y .snd .fst )

  -- ================================================================
  -- THE LEMMA THE WHOLE QUESTION IS ABOUT.
  -- ================================================================

  dec-at : (Γ : Ctx) (C : Ty)
         → ((A B : Ty) → (Infer Γ A & Infer Γ B) ⊢ Kty A B)
         → Dec⟨ Syn Γ ⟩ ⊢ Dec⟨ Infer Γ C ⟩
  dec-at Γ C uniq t (inr k) = dec-no (Infer Γ C) t λ d → k (C , d)
  dec-at Γ C uniq t (inl (A , d)) with dec-⌈⌉ᵗ C A tt
  ... | inl e = dec-yes (Infer Γ C) t (tyCast (λ X → Infer Γ X) A C e t d)
  ... | inr k = dec-no  (Infer Γ C) t λ d' → k (uniq A C t (d , d'))

  -- ================================================================
  -- The checking side's lambda rule.
  -- ================================================================

  LamCase : Ctx → Ty → TmG
  LamCase Γ C = ⊕ᴰ (IsArr C) (λ sa →
    ⊕ᴰ Name (λ n → LamG (Nm n) (Check ((n , dom sa) ∷ Γ) (cod sa))))

  module _ (Γ : Ctx) (C : Ty) (t : Raw) where

    private
      Q : IsArr C → TmG
      Q sa = ⊕ᴰ Name (λ n → LamG (Nm n) (Check ((n , dom sa) ∷ Γ) (cod sa)))

      P : IsArr C → Name → TmG
      P sa n = Check ((n , dom sa) ∷ Γ) (cod sa)

    dec-lamCase : ((sa : IsArr C) (sp : IsLam t)
                   → Dec⟨ P sa (TParts lamOp t sp true) ⟩
                          (TParts lamOp t sp false))
                → Dec⟨ LamCase Γ C ⟩ t
    dec-lamCase d with ⊗-decSplit arrOp C tt
    ... | inr k = dec-no (LamCase Γ C) t λ y → k (y .fst , λ _ → tt)
    ... | inl x = at (x .fst)
      where
      at : (sa : IsArr C) → Dec⟨ LamCase Γ C ⟩ t
      at sa with dec-map (LamGᵈ (P sa)) (Q sa) lam-collapse⁻ lam-collapse t
                         (dec-lamᵈ (P sa) t (d sa))
      ... | inl q = dec-yes (LamCase Γ C) t (sa , q)
      ... | inr k = dec-no  (LamCase Γ C) t λ y →
        k (subst (λ s → Q s t) (Split-isProp arrOp C (y .fst) sa) (y .snd))

  -- ================================================================
  -- The typechecker.
  -- ================================================================

  DecJ : TmG
  DecJ = &ᴰ Ctx (λ Γ → Dec⟨ Syn Γ ⟩)
       & &ᴰ (Ctx × Ty) (λ p → Dec⟨ Check (p .fst) (p .snd) ⟩)

  typecheck : ⊤G ⊢ DecJ
  typecheck t _ = recSize {M = DecJ} step t
    where
    step : (t : Raw) → ((s : Raw) → size s < size t → DecJ s) → DecJ t
    step t rec = dS , dC
      where
      recSyn : (s : Raw) → size s < size t → (Γ : Ctx) → Dec⟨ Syn Γ ⟩ s
      recSyn s p Γ = rec s p .fst Γ

      recChk : (s : Raw) → size s < size t → (Γ : Ctx) (C : Ty)
             → Dec⟨ Check Γ C ⟩ s
      recChk s p Γ C = rec s p .snd (Γ , C)

      dS : (Γ : Ctx) → Dec⟨ Syn Γ ⟩ t
      dS Γ = dec-map (SynStep Γ) (Syn Γ) (syn-in Γ) (syn-out Γ) t
        (dec-⊕ (VarG (Look Γ)) (SynApp Γ ⊕ SynAnn Γ) t
          ( dec-⊗ varOp (varFam (Look Γ)) t
              (λ sp a → dec-Look Γ (TParts varOp t sp a) tt)
          , dec-⊕ (SynApp Γ) (SynAnn Γ) t
              ( dec-map (AppGᵈ Γ) (SynApp Γ) (app-collapse⁻ Γ) (app-collapse Γ) t
                  (dec-appᵈ Γ t
                    (λ sp → recSyn (TParts appOp t sp true)
                                   (proper appOp t sp true) Γ)
                    (λ sp A₀ → recChk (TParts appOp t sp false)
                                      (proper appOp t sp false) Γ A₀))
              , dec-map (AnnGᵈ (Check Γ)) (SynAnn Γ)
                        ann-collapse⁻ ann-collapse t
                  (dec-annᵈ (Check Γ) t
                    (λ sp → recChk (TParts annOp t sp true)
                                   (proper annOp t sp true) Γ
                                   (TParts annOp t sp false)))
              )))

      dC : (p : Ctx × Ty) → Dec⟨ Check (p .fst) (p .snd) ⟩ t
      dC (Γ , C) =
        dec-map (JStep Jμ (chk , Γ , C)) (Check Γ C)
                (j-roll (chk , Γ , C)) (j-unroll (chk , Γ , C)) t
          (dec-⊕ (Infer Γ C) (LamCase Γ C) t
            ( dec-at Γ C (synUnique Γ) t (dS Γ)
            , dec-lamCase Γ C t
                (λ sa sp → recChk (TParts lamOp t sp false)
                                  (proper lamOp t sp false)
                                  ((TParts lamOp t sp true , dom sa) ∷ Γ)
                                  (cod sa))
            ))

  -- ================================================================
  -- The two modes, and the closed case.
  -- ================================================================

  infer? : ⊤G ⊢ &ᴰ Ctx (λ Γ → Dec⟨ Syn Γ ⟩)
  infer? = &-E₁ ∘g typecheck

  check? : ⊤G ⊢ &ᴰ (Ctx × Ty) (λ p → Dec⟨ Check (p .fst) (p .snd) ⟩)
  check? = &-E₂ ∘g typecheck

  closed-infer? : ⊤G ⊢ Dec⟨ Syn [] ⟩
  closed-infer? = &ᴰ-E Ctx [] ∘g infer?

  closed-check? : (C : Ty) → ⊤G ⊢ Dec⟨ Check [] C ⟩
  closed-check? C = &ᴰ-E (Ctx × Ty) ([] , C) ∘g check?
