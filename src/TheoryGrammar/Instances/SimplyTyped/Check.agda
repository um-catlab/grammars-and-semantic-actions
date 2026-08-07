{-
  THE BIDIRECTIONAL TYPECHECKER, as one map of the calculus:

      typecheck : ⊤ ⊢   &ᴰ Ctx      (λ Γ     → Dec⟨ Syn Γ ⟩)
                      & &ᴰ (Ctx×Ty) (λ (Γ,C) → Dec⟨ Check Γ C ⟩)

  Both modes at once, for every context: the context grows while the
  term shrinks, so neither recursion closes on its own.  `infer?` and
  `check?` are its two projections.

  The load-bearing lemma is `dec-at`.  Deciding "synthesises SOME type"
  gives deciding "synthesises THIS type" ONLY GIVEN the subsingleton
  hypothesis, which is an EXPLICIT argument so that the dependency is a
  theorem and not a remark.

  MEASUREMENT.  `Unique.synUnique` is consumed in exactly THREE places
  here, all of them REFUTATIONS: twice in `dec-appᵈ` (the function
  synthesised a non-arrow; the argument failed at its domain) and once
  in `dec-at`.  Nothing positive uses it.

  Two decisions are written out by hand -- `dec-appᵈ` (see
  `Dependent.agda` for why it is not there) and `dec-lamCase` -- and the
  generic decision layer does everything else.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Check where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
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
  -- The application's dependent tensor: the argument's checking type
  -- comes from the FUNCTION's slot, and there is no representable
  -- pinning it, so this is where uniqueness has to be used.
  --
  -- (`SynStep`/`syn-out`/`syn-in` -- the unfolding this collapses --
  -- live in `Judgments.agda` beside `JStep`, since they decide nothing.)
  -- ================================================================

  -- `AppGᵈ Γ` denotes "the term is an application whose function
  -- synthesises SOME arrow and whose argument checks at that arrow's
  -- domain".  Both slots are read off the one splitting the witness
  -- carries, so the two types are the same guess, not two guesses.
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

    -- `Payload sp` denotes what an `AppGᵈ` witness carries once its
    -- splitting is known to be `sp`: the guessed arrow, and the two
    -- derivations at that arrow.
    Payload : IsApp t → Type₀
    Payload sp =
      Σ[ AB ∈ Ty × Ty ]
        ( Infer Γ (AB .fst ⇒ᵗ AB .snd) (TParts appOp t sp true)
        × Check Γ (AB .fst) (TParts appOp t sp false) )

    -- any witness splits the same way, by unique readability, so its
    -- payload can be read AT a splitting chosen elsewhere
    align : (sp : IsApp t) → AppGᵈ Γ t → Payload sp
    align sp y = subst Payload (Split-isProp appOp t (y .fst) sp) (y .snd)

    -- a payload CARRIES a synthesis derivation for the function slot,
    -- at the arrow it guessed.  Every refutation below consumes exactly
    -- this, so it is named once rather than rebuilt at each use.
    payload-syn : (sp : IsApp t) → Payload sp → Syn Γ (TParts appOp t sp true)
    payload-syn sp p = (p .fst .fst ⇒ᵗ p .fst .snd) , p .snd .fst

    dec-appᵈ : ((sp : IsApp t) → Dec⟨ Syn Γ ⟩ (TParts appOp t sp true))
             → ((sp : IsApp t) (A₀ : Ty)
                → Dec⟨ Check Γ A₀ ⟩ (TParts appOp t sp false))
             → Dec⟨ AppGᵈ Γ ⟩ t
    dec-appᵈ dFn dArg =
      dec-elim (⊗ˢ appOp (λ _ → ⊤G)) t
        (λ x → fromFn (x .fst) (dFn (x .fst)))
        (λ k → dec-no (AppGᵈ Γ) t λ y → k (y .fst , λ _ → tt))
        (⊗-decSplit appOp t tt)
      where
      -- the function's type is an arrow, and the argument checks at its
      -- domain: the only positive case
      atArrow : (sp : IsApp t) (A₁ B₁ : Ty)
              → Infer Γ (A₁ ⇒ᵗ B₁) (TParts appOp t sp true)
              → Dec⟨ Check Γ A₁ ⟩ (TParts appOp t sp false)
              → Dec⟨ AppGᵈ Γ ⟩ t
      atArrow sp A₁ B₁ d =
        dec-elim (Check Γ A₁) (TParts appOp t sp false)
          (λ c → dec-yes (AppGᵈ Γ) t (sp , (A₁ , B₁) , d , c))
          (λ k → dec-no (AppGᵈ Γ) t λ y → k (atDomain (align sp y)))
        where
        -- SUBSINGLETON AT WORK (1): the payload's own domain IS `A₁`,
        -- by uniqueness of the synthesised type and then injectivity of
        -- the arrow in its LEFT argument.
        atDomain : Payload sp → Check Γ A₁ (TParts appOp t sp false)
        atDomain p =
          subst (λ X → Check Γ X (TParts appOp t sp false))
                (sym (⇒ᵗ-injˡ A₁ B₁ (p .fst .fst) (p .fst .snd)
                       (synUnique Γ (A₁ ⇒ᵗ B₁) (payload-syn sp p .fst)
                                  (TParts appOp t sp true)
                                  (d , p .snd .fst))))
                (p .snd .snd)

      atType : (sp : IsApp t) (C : Ty)
             → Infer Γ C (TParts appOp t sp true) → Dec⟨ AppGᵈ Γ ⟩ t
      atType sp base d = dec-no (AppGᵈ Γ) t λ y → E.rec (notArrow (align sp y))
        where
        -- SUBSINGLETON AT WORK (2): the synthesised type is the ONLY
        -- one, so "it is not an arrow" really does refute the
        -- application.  Without uniqueness this branch is unprovable.
        notArrow : Payload sp → E.⊥
        notArrow p =
          base≢arr (p .fst .fst) (p .fst .snd)
            (synUnique Γ base (payload-syn sp p .fst)
                       (TParts appOp t sp true) (d , p .snd .fst))
      atType sp (A₁ ⇒ᵗ B₁) d = atArrow sp A₁ B₁ d (dArg sp A₁)

      fromFn : (sp : IsApp t) → Dec⟨ Syn Γ ⟩ (TParts appOp t sp true)
             → Dec⟨ AppGᵈ Γ ⟩ t
      fromFn sp =
        dec-elim (Syn Γ) (TParts appOp t sp true)
          (λ z → atType sp (z .fst) (z .snd))
          (λ k → dec-no (AppGᵈ Γ) t λ y → k (payload-syn sp (align sp y)))

  -- ================================================================
  -- THE LEMMA THE WHOLE QUESTION IS ABOUT.
  -- ================================================================

  -- `dec-at Γ C uniq` denotes: given a decision of "synthesises SOME
  -- type", a decision of "synthesises `C`".  The uniqueness hypothesis
  -- is EXPLICIT, and it is used only on the refutation side -- without
  -- it one can decide "some type" but cannot refute "THIS type".
  --
  -- The OUTER decision is uniform in the index, so it is the ordinary
  -- `⊕-E`, and the ⊕ᴰ that guesses the synthesised type is `⊕ᴰ-E`.
  -- Only the INNER one -- "is the synthesised type the one asked for?"
  -- -- sits at a fixed index (that very type), and takes `dec-elim`.
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

  -- ================================================================
  -- The checking side's lambda rule.
  -- ================================================================

  -- `LamCase Γ C` denotes the `lam` alternative of `Check Γ C`: the
  -- checking type SPLITS as an arrow, and the body checks at its
  -- codomain under the binder.  The `⊕ᴰ (IsArr C)` is the promodel's
  -- own `Split arrOp C`, so no case analysis on `Ty` appears.
  LamCase : Ctx → Ty → TmG
  LamCase Γ C = ⊕ᴰ (IsArr C) (λ sa →
    ⊕ᴰ Name (λ n → LamG (Nm n) (Check ((n , dom sa) ∷ Γ) (cod sa))))

  module _ (Γ : Ctx) (C : Ty) (t : Raw) where

    private
      -- the alternative at a fixed arrow-splitting, and its body
      Q : IsArr C → TmG
      Q sa = ⊕ᴰ Name (λ n → LamG (Nm n) (Check ((n , dom sa) ∷ Γ) (cod sa)))

      P : IsArr C → Name → TmG
      P sa n = Check ((n , dom sa) ∷ Γ) (cod sa)

    dec-lamCase : ((sa : IsArr C) (sp : IsLam t)
                   → Dec⟨ P sa (TParts lamOp t sp true) ⟩
                          (TParts lamOp t sp false))
                → Dec⟨ LamCase Γ C ⟩ t
    dec-lamCase d =
      dec-elim (⊗ˢ arrOp (λ _ → ⊤G)) C
        (λ x → at (x .fst))
        (λ k → dec-no (LamCase Γ C) t λ y → k (y .fst , λ _ → tt))
        (⊗-decSplit arrOp C tt)
      where
      at : (sa : IsArr C) → Dec⟨ LamCase Γ C ⟩ t
      at sa =
        dec-elim (Q sa) t
          (λ q → dec-yes (LamCase Γ C) t (sa , q))
          (λ k → dec-no (LamCase Γ C) t λ y →
             k (subst (λ s → Q s t)
                      (Split-isProp arrOp C (y .fst) sa) (y .snd)))
          (dec-map (LamGᵈ (P sa)) (Q sa) lam-collapse⁻ lam-collapse t
                   (dec-lamᵈ (P sa) t (d sa)))

  -- ================================================================
  -- The typechecker.
  -- ================================================================

  -- `DecJ` denotes both modes decided at once, at every context and
  -- every checking type.  The `&` is not a conjunctive statement to be
  -- split: the two recursions are MUTUAL -- a `chk` node's body is
  -- decided at a longer context, and a `syn` node's function slot is
  -- decided in `chk` -- so neither half is provable alone.  `infer?`
  -- and `check?` below are the projections a caller wants.
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
