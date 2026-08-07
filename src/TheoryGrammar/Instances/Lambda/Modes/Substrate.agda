{-
  A CONTEXT PROMODEL FROM A TERNARY RELATION ON LISTS.

  DENOTES: `R u v Γ` reads "Γ decomposes as u beside v".  The three
  substrates differ only in R; collected here is all that does not --

    fib, point  the promodel and its (lax) total point
    Fam, Slots  a two-slot grammar family; one splitting's payload
    slots       rebuild a slot function, one slot at a time
    decSp       ONE splitting decided from its two slots; `decNil`
                finishes `[]`, which `nilJ` says splits exactly once
    Step        one constructor of R as a recursive step: `out`/`into`
                move a witness across it, `chain` recurses

  A substrate owes exactly its constructors: that residue IS the
  difference between ordered, linear and relevant.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Substrate where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.Lambda.Modes.Ctx

module Substrate
  (Name : Type₀)
  -- `R u v Γ` : "Γ decomposes as u beside v"
  (R : List Name → List Name → List Name → Type₀)
  -- the empty context decomposes
  (rnil : R [] [] [])
  -- every concatenation decomposes as its two halves: what makes the
  -- point below TOTAL.  Nothing forces the converse, so the containment
  -- may be strict.
  (rApp : (u v : List Name) → R u v (u ++ v))
  -- `[]` decomposes exactly one way, in the STRICT sense: the eliminator
  -- is definitional, so the refutation it feeds still reduces.
  (nilJ : ∀ {ℓ} (M : (u v : List Name) → R u v [] → Type ℓ)
        → M [] [] rnil → (u v : List Name) (r : R u v []) → M u v r)
  where

  Ctx : Type₀
  Ctx = List Name

  -- a splitting of Γ IS a decomposition of it
  CSplit : (o : CtxOp) → Ctx → Type₀
  CSplit mul Γ = Σ[ u ∈ Ctx ] Σ[ v ∈ Ctx ] R u v Γ

  -- ... and its parts are the two sides, read off by slot
  CParts : (o : CtxOp) (Γ : Ctx) → CSplit o Γ → CtxAr o → Ctx
  CParts mul Γ (u , v , _) b = if b then u else v

  -- The promodel.  `Split` is the whole content: it says WHICH
  -- decompositions count, and `parts` only projects.
  fib : Fibered ctxSig ℓ-zero ℓ-zero
  fib .carrier _ = Ctx
  fib .Split     = CSplit
  fib .parts     = CParts

  -- The total point, separately from `fib`.  Its containment may be
  -- STRICT -- `R u v w` need not imply `u ++ v ≡ w` -- so this really is
  -- a lax point, and the multiplicative layer never consults it.
  --
  -- `parts-split` is the one law, and what it forces is that reading the
  -- parts off the canonical splitting of `op f` gives back `f`.  It
  -- costs `funExt` because `Bool` has no definitional eta.
  point : LaxPoint fib
  point .op mul f          = f true ++ f false
  point .split mul f       = f true , f false , rApp (f true) (f false)
  point .parts-split mul f = funExt λ { true → refl ; false → refl }

  open DecFib fib public

  -- a slot family for `mul`: one grammar per side of a split
  Fam : Type₁
  Fam = CtxAr mul → TheoryTy ℓ-zero tt

  -- the payload of ONE splitting: `A true` of the left part and
  -- `A false` of the right, packaged as a function of the slot
  Slots : (A : Fam) (Γ : Ctx) → CSplit mul Γ → Type₀
  Slots A Γ sp = (b : CtxAr mul) → A b (CParts mul Γ sp b)

  -- `Bool` has no definitional eta, so a slot function cannot be reused
  -- across a re-indexing of the parts even when it matches slotwise: it
  -- has to be rebuilt.  Every repackaging below is one call of this.
  slots : (A : Fam) (P : CtxAr mul → Ctx)
        → A true (P true) → A false (P false) → (b : CtxAr mul) → A b (P b)
  slots A P p q true  = p
  slots A P p q false = q

  -- ================================================================
  -- One splitting, decided from its two slots.
  -- ================================================================

  -- DENOTES: "this ONE decomposition either carries the payload or
  -- provably does not".  `hit` gets the payload, `miss` gets its
  -- refutation; neither branch sees a sum, because `dec-elim` does.
  decSp : ∀ {ℓZ} (A : Fam) (Γ : Ctx) (sp : CSplit mul Γ) {Z : Type ℓZ}
        → (Slots A Γ sp → Z)
        → ((Slots A Γ sp → ⊥G {tt} Γ) → Z)
        → Dec⟨ A true ⟩ (CParts mul Γ sp true)
        → Dec⟨ A false ⟩ (CParts mul Γ sp false)
        → Z
  decSp A Γ sp hit miss dt df =
    dec-elim (A true) (CParts mul Γ sp true)
      (λ p → dec-elim (A false) (CParts mul Γ sp false)
               (λ q → hit (slots A (CParts mul Γ sp) p q))
               (λ k → miss (λ h → k (h false)))
               df)
      (λ k → miss (λ h → k (h true)))
      dt

  -- ================================================================
  -- The empty context: one splitting, so `decSp` finishes it.
  -- ================================================================

  nilSp : CSplit mul []
  nilSp = [] , [] , rnil

  -- every witness at `[]` is a witness at `nilSp`: `nilJ` in payload form
  nilSlots : (A : Fam) → ⊗ˢ mul A [] → Slots A [] nilSp
  nilSlots A ((u , v , r) , h) =
    nilJ (λ u v r → ((b : CtxAr mul) → A b (if b then u else v))
                  → Slots A [] nilSp)
         (λ h' → h') u v r h

  decNil : (A : Fam)
         → ((sp : CSplit mul []) (b : CtxAr mul) → Dec⟨ A b ⟩ (CParts mul [] sp b))
         → Dec⟨ ⊗ˢ mul A ⟩ []
  decNil A d =
    decSp A [] nilSp
      (λ h → dec-yes (⊗ˢ mul A) [] (nilSp , h))
      (λ k → dec-no (⊗ˢ mul A) [] (λ w → k (nilSlots A w)))
      (d nilSp true) (d nilSp false)

  -- ================================================================
  -- One constructor of `R`, as a recursive step.  `con` moves the head
  -- name into the slots named by `sL`/`sR`; the recursive call then runs
  -- at `fam`, the caller's family with that shift built in.
  -- ================================================================

  module Step (x : Name) (Γ : Ctx) (A : Fam)
              (sL sR : Ctx → Ctx)
              (con : {u v : Ctx} → R u v Γ → R (sL u) (sR v) (x ∷ Γ))
    where

    -- the caller's family, pre-composed with the shift this constructor
    -- performs: "A, as seen from before the head was moved"
    fam : Fam
    fam b Δ = A b (if b then sL Δ else sR Δ)

    -- a decomposition of Γ, pushed through `con` to one of `x ∷ Γ`
    shifted : (u v : Ctx) (r : R u v Γ) → CSplit mul (x ∷ Γ)
    shifted u v r = sL u , sR v , con r

    -- the caller's slot decisions, handed down
    down : ((sp : CSplit mul (x ∷ Γ)) (b : CtxAr mul)
            → Dec⟨ A b ⟩ (CParts mul (x ∷ Γ) sp b))
         → (sp : CSplit mul Γ) (b : CtxAr mul) → Dec⟨ fam b ⟩ (CParts mul Γ sp b)
    down d (u , v , r) =
      slots (λ b → Dec⟨ fam b ⟩) (CParts mul Γ (u , v , r))
            (d (shifted u v r) true) (d (shifted u v r) false)

    -- a witness at the recursive call is a witness here ...
    out : ⊗ˢ mul fam Γ → ⊗ˢ mul A (x ∷ Γ)
    out ((u , v , r) , h) =
      shifted u v r
      , slots A (CParts mul (x ∷ Γ) (shifted u v r)) (h true) (h false)

    -- ... and conversely, which is what the refutation branch needs
    into : (u v : Ctx) (r : R u v Γ)
         → Slots A (x ∷ Γ) (shifted u v r) → ⊗ˢ mul fam Γ
    into u v r h =
      (u , v , r) , slots fam (CParts mul Γ (u , v , r)) (h true) (h false)

    -- THE GLUE, shared by all three substrates: consume the recursive
    -- decision at `fam`.  A witness there is a witness here (`out`); a
    -- refutation is handed to `k`, which either tries the next
    -- constructor or -- when they are exhausted -- refutes them all.
    chain : ((¬G (⊗ˢ mul fam)) Γ → Dec⟨ ⊗ˢ mul A ⟩ (x ∷ Γ))
          → Dec⟨ ⊗ˢ mul fam ⟩ Γ
          → Dec⟨ ⊗ˢ mul A ⟩ (x ∷ Γ)
    chain k =
      dec-elim (⊗ˢ mul fam) Γ
        (λ w → dec-yes (⊗ˢ mul A) (x ∷ Γ) (out w)) k
