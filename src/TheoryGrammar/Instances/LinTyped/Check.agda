{- THE BIDIRECTIONAL LINEAR TYPECHECKER, as one map of the calculus:
   typecheck : ⊤ ⊢ &ᴰ Ctx (λ Γ → Dec⟨ Syn Γ ⟩) & &ᴰ (Ctx×Ty) (λ (Γ,C) →
   Dec⟨ Check Γ C ⟩) Both modes at once, for every context: the context
   grows while the term shrinks, so neither recursion closes on its own. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Check where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered
open import TheoryGrammar.Instances.LinTyped.Base
open import TheoryGrammar.Instances.LinTyped.Grading
open import TheoryGrammar.Instances.LinTyped.Readable
open import TheoryGrammar.Instances.LinTyped.Types
open import TheoryGrammar.Instances.LinTyped.Context
open import TheoryGrammar.Instances.LinTyped.Judgments
open import TheoryGrammar.Instances.LinTyped.Unique

-- THE ANNOTATION'S DEPENDENT TENSOR. The annotation TYPE determines what
-- is checked, and the representable `⌈ A ⌉` pins the guess, so the `⊕ᴰ`
-- that guesses it collapses.

AnnGᵈ : (Ty → TmG) → TmG
AnnGᵈ P t = Σ[ sp ∈ IsAnn t ]
              P (TParts annOp t sp false) (TParts annOp t sp true)

ann-collapse : {P : Ty → TmG}
             → ⊕ᴰ Ty (λ A → AnnG (P A) (⌈_⌉ {s = ty} A)) ⊢ AnnGᵈ P
ann-collapse _ (A , sp , h) with h false
... | Eq.refl = sp , h true

-- PRIMITIVE (phase 1): the `⊕ᴰ` tag is READ OFF the splitting, so it
-- varies with the world; `⊕ᴰ-I` takes a tag fixed in advance.  This is
-- `⌈⌉-UP` -- Yoneda -- at a SLOT rather than at the whole.
ann-collapse⁻ : {P : Ty → TmG}
              → AnnGᵈ P ⊢ ⊕ᴰ Ty (λ A → AnnG (P A) (⌈_⌉ {s = ty} A))
ann-collapse⁻ t (sp , a) =
  TParts annOp t sp false , sp , λ { true → a ; false → Eq.refl }

dec-annᵈ-at : (P : Ty → TmG) (t : Raw) (sp : IsAnn t)
            → Dec⟨ P (TParts annOp t sp false) ⟩ (TParts annOp t sp true)
            → Dec⟨ AnnGᵈ P ⟩ t
dec-annᵈ-at P t sp =
  dec-elim (P (TParts annOp t sp false)) (TParts annOp t sp true)
    (λ a → dec-yes (AnnGᵈ P) t (sp , a))
    (λ k → dec-no (AnnGᵈ P) t λ x →
       k (subst (λ s → P (TParts annOp t s false) (TParts annOp t s true))
                (Split-isProp annOp t (x .fst) sp) (x .snd)))

dec-annᵈ : (P : Ty → TmG) (t : Raw)
         → ((sp : IsAnn t)
            → Dec⟨ P (TParts annOp t sp false) ⟩ (TParts annOp t sp true))
         → Dec⟨ AnnGᵈ P ⟩ t
dec-annᵈ P t d =
  dec-elim (⊗ˢ annOp (λ _ → ⊤G)) t
    (λ x → dec-annᵈ-at P t (x .fst) (d (x .fst)))
    (λ k → dec-no (AnnGᵈ P) t λ y → k (y .fst , λ _ → tt))
    (⊗-decSplit annOp t tt)

-- THE APPLICATION'S DEPENDENT TENSOR, at a FIXED splitting of the context.

AppGᵈ : Ctx → Ctx → TmG
AppGᵈ Γ₁ Γ₂ = ⊗ˢᵈ appOp λ ps →
  Σ[ AB ∈ Ty × Ty ]
    ( Infer Γ₁ (AB .fst ⊸ᵗ AB .snd) (ps true)
    × Check Γ₂ (AB .fst) (ps false) )

-- PRIMITIVE (phase 1), and the whole residue of the collapse: arities
-- have no η, so turning a slotwise payload into a pair is not free.
-- Moving `⊕ᴰ` past the splitting IS free (`Fibered.⊕ᴰ-⊗ˢᵈ-out/-in`).
private
  boolUncurry : {F : Bool → Type₀} → ((a : Bool) → F a) → F true × F false
  boolUncurry h = h true , h false

  SlotP : Ctx → Ctx → Ty × Ty → Parts appOp → Type₀
  SlotP Γ₁ Γ₂ AB ps =
    (a : TAr appOp)
    → appFam (Infer Γ₁ (AB .fst ⊸ᵗ AB .snd)) (Check Γ₂ (AB .fst)) a (ps a)

  PairP : Ctx → Ctx → Parts appOp → Type₀
  PairP Γ₁ Γ₂ ps =
    Σ[ AB ∈ Ty × Ty ]
      ( Infer Γ₁ (AB .fst ⊸ᵗ AB .snd) (ps true)
      × Check Γ₂ (AB .fst) (ps false) )

app-collapse : (Γ₁ Γ₂ : Ctx) → ⊕ᴰ (Ty × Ty) (QApp Γ₁ Γ₂) ⊢ AppGᵈ Γ₁ Γ₂
app-collapse Γ₁ Γ₂ =
  ⊗ˢᵈ-E appOp (λ ps → Σ[ AB ∈ Ty × Ty ] SlotP Γ₁ Γ₂ AB ps)
        (λ t sp → λ { (AB , h) → sp , AB , boolUncurry h })
  ∘⊢ ⊕ᴰ-⊗ˢᵈ-out appOp (Ty × Ty) (SlotP Γ₁ Γ₂)

app-collapse⁻ : (Γ₁ Γ₂ : Ctx) → AppGᵈ Γ₁ Γ₂ ⊢ ⊕ᴰ (Ty × Ty) (QApp Γ₁ Γ₂)
app-collapse⁻ Γ₁ Γ₂ =
  ⊕ᴰ-⊗ˢᵈ-in appOp (Ty × Ty) (SlotP Γ₁ Γ₂)
  ∘⊢ ⊗ˢᵈ-E appOp (PairP Γ₁ Γ₂)
            (λ t sp → λ { (AB , d , c) → sp , AB , boolΠ d c })

module _ (Γ₁ Γ₂ : Ctx) (t : Raw) where

  -- what an `AppGᵈ` witness carries once its splitting is known
  Payload : IsApp t → Type₀
  Payload sp =
    Σ[ AB ∈ Ty × Ty ]
      ( Infer Γ₁ (AB .fst ⊸ᵗ AB .snd) (TParts appOp t sp true)
      × Check Γ₂ (AB .fst) (TParts appOp t sp false) )

  -- any witness splits the same way, by unique readability
  align : (sp : IsApp t) → AppGᵈ Γ₁ Γ₂ t → Payload sp
  align sp y = subst Payload (Split-isProp appOp t (y .fst) sp) (y .snd)

  payload-syn : (sp : IsApp t) → Payload sp → Syn Γ₁ (TParts appOp t sp true)
  payload-syn sp p = (p .fst .fst ⊸ᵗ p .fst .snd) , p .snd .fst

  dec-appᵈ : ((sp : IsApp t) → Dec⟨ Syn Γ₁ ⟩ (TParts appOp t sp true))
           → ((sp : IsApp t) (A₀ : Ty)
              → Dec⟨ Check Γ₂ A₀ ⟩ (TParts appOp t sp false))
           → Dec⟨ AppGᵈ Γ₁ Γ₂ ⟩ t
  dec-appᵈ dFn dArg =
    dec-elim (⊗ˢ appOp (λ _ → ⊤G)) t
      (λ x → fromFn (x .fst) (dFn (x .fst)))
      (λ k → dec-no (AppGᵈ Γ₁ Γ₂) t λ y → k (y .fst , λ _ → tt))
      (⊗-decSplit appOp t tt)
    where
    atArrow : (sp : IsApp t) (A₁ B₁ : Ty)
            → Infer Γ₁ (A₁ ⊸ᵗ B₁) (TParts appOp t sp true)
            → Dec⟨ Check Γ₂ A₁ ⟩ (TParts appOp t sp false)
            → Dec⟨ AppGᵈ Γ₁ Γ₂ ⟩ t
    atArrow sp A₁ B₁ d =
      dec-elim (Check Γ₂ A₁) (TParts appOp t sp false)
        (λ c → dec-yes (AppGᵈ Γ₁ Γ₂) t (sp , (A₁ , B₁) , d , c))
        (λ k → dec-no (AppGᵈ Γ₁ Γ₂) t λ y → k (atDomain (align sp y)))
      where
      -- SUBSINGLETON AT WORK (1): the payload's own domain IS `A₁`.
      atDomain : Payload sp → Check Γ₂ A₁ (TParts appOp t sp false)
      atDomain p =
        subst (λ X → Check Γ₂ X (TParts appOp t sp false))
              (sym (⊸-injˡ A₁ B₁ (p .fst .fst) (p .fst .snd)
                     (synUnique Γ₁ (A₁ ⊸ᵗ B₁) (payload-syn sp p .fst)
                                (TParts appOp t sp true)
                                (d , p .snd .fst))))
              (p .snd .snd)

    atType : (sp : IsApp t) (C : Ty)
           → Infer Γ₁ C (TParts appOp t sp true) → Dec⟨ AppGᵈ Γ₁ Γ₂ ⟩ t
    atType sp base d =
      dec-no (AppGᵈ Γ₁ Γ₂) t λ y → E.rec (notArrow (align sp y))
      where
      -- SUBSINGLETON AT WORK (2): the synthesised type is the ONLY one,
      -- so "it is not a lollipop" really does refute the application.
      notArrow : Payload sp → E.⊥
      notArrow p =
        base≢lol (p .fst .fst) (p .fst .snd)
          (synUnique Γ₁ base (payload-syn sp p .fst)
                     (TParts appOp t sp true) (d , p .snd .fst))
    atType sp (A₁ ⊸ᵗ B₁) d = atArrow sp A₁ B₁ d (dArg sp A₁)

    fromFn : (sp : IsApp t) → Dec⟨ Syn Γ₁ ⟩ (TParts appOp t sp true)
           → Dec⟨ AppGᵈ Γ₁ Γ₂ ⟩ t
    fromFn sp =
      dec-elim (Syn Γ₁) (TParts appOp t sp true)
        (λ z → atType sp (z .fst) (z .snd))
        (λ k → dec-no (AppGᵈ Γ₁ Γ₂) t λ y → k (payload-syn sp (align sp y)))

-- THE LEMMA THE WHOLE QUESTION IS ABOUT.

dec-at : (Γ : Ctx) (C : Ty)
       → ((A B : Ty) → (Infer Γ A & Infer Γ B) ⊢ Kty A B)
       → Dec⟨ Syn Γ ⟩ ⊢ Dec⟨ Infer Γ C ⟩
dec-at Γ C uniq =
  ⊕-E (⊕ᴰ-E λ A t d →
         dec-elim (⌈_⌉ {s = ty} C) A
           (λ e → dec-yes (Infer Γ C) t
                    (tyCast (λ X → Infer Γ X) A C e t d))
           (λ k → dec-no (Infer Γ C) t λ d' → k (uniq A C t (d , d')))
           (dec-⌈⌉ᵗ C A tt))
      (dec-no (Infer Γ C) ∘g ¬G-map (⊕ᴰ-I Ty {A = Infer Γ} C))

-- The checking side's lambda rule.  Simpler than the cartesian one:
-- the binder has no name slot, so `LamG` is a UNARY tensor and the
-- decision is `dec-⊗ lamOp` with no dependent tensor in sight.

LamCase : Ctx → Ty → TmG
LamCase Γ C =
  ⊕ᴰ (IsLol C) (λ sa → LamG (Check (just (dom sa) ∷ Γ) (cod sa)))

module _ (Γ : Ctx) (C : Ty) (t : Raw) where

  private
    Q : IsLol C → TmG
    Q sa = LamG (Check (just (dom sa) ∷ Γ) (cod sa))

    P : IsLol C → TmG
    P sa = Check (just (dom sa) ∷ Γ) (cod sa)

  dec-lamCase : ((sa : IsLol C) (sp : IsLam t)
                 → Dec⟨ P sa ⟩ (TParts lamOp t sp tt))
              → Dec⟨ LamCase Γ C ⟩ t
  dec-lamCase d =
    dec-elim (⊗ˢ lolOp (λ _ → ⊤G)) C
      (λ x → at (x .fst))
      (λ k → dec-no (LamCase Γ C) t λ y → k (y .fst , λ _ → tt))
      (⊗-decSplit lolOp C tt)
    where
    at : (sa : IsLol C) → Dec⟨ LamCase Γ C ⟩ t
    at sa =
      dec-elim (Q sa) t
        (λ q → dec-yes (LamCase Γ C) t (sa , q))
        (λ k → dec-no (LamCase Γ C) t λ y →
           k (subst (λ s → Q s t)
                    (Split-isProp lolOp C (y .fst) sa) (y .snd)))
        (dec-⊗ lamOp (lamFam (P sa)) t (λ sp a → d sa sp))

-- The typechecker.

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
            ( dec-SplitG Γ (λ Γ₁ Γ₂ → ⊕ᴰ (Ty × Ty) (QApp Γ₁ Γ₂)) t
                (λ Γ₁ Γ₂ →
                   dec-map (AppGᵈ Γ₁ Γ₂) (⊕ᴰ (Ty × Ty) (QApp Γ₁ Γ₂))
                           (app-collapse⁻ Γ₁ Γ₂) (app-collapse Γ₁ Γ₂) t
                     (dec-appᵈ Γ₁ Γ₂ t
                       (λ sp → recSyn (TParts appOp t sp true)
                                      (proper appOp t sp true) Γ₁)
                       (λ sp A₀ → recChk (TParts appOp t sp false)
                                         (proper appOp t sp false) Γ₂ A₀)))
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
              (λ sa sp → recChk (TParts lamOp t sp tt)
                                (proper lamOp t sp tt)
                                (just (dom sa) ∷ Γ) (cod sa))
          ))

-- The two modes, and the closed case.

infer? : ⊤G ⊢ &ᴰ Ctx (λ Γ → Dec⟨ Syn Γ ⟩)
infer? = &-E₁ ∘g typecheck

check? : ⊤G ⊢ &ᴰ (Ctx × Ty) (λ p → Dec⟨ Check (p .fst) (p .snd) ⟩)
check? = &-E₂ ∘g typecheck

closed-infer? : ⊤G ⊢ Dec⟨ Syn [] ⟩
closed-infer? = &ᴰ-E Ctx [] ∘g infer?

closed-check? : (C : Ty) → ⊤G ⊢ Dec⟨ Check [] C ⟩
closed-check? C = &ᴰ-E (Ctx × Ty) ([] , C) ∘g check?
