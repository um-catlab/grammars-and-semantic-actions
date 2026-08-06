{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CUT SEARCH, CONFINED.

  The statement being established is INTERNAL:

      ⊗-EM cat A  =  ⊤G ⊢ ((⊗ˢ cat A) ⊕ ¬G (⊗ˢ cat A))

  i.e. `Probe (A ⊗ᶜ B)` -- "at every span, a cut that works or a proof
  that none does".  `TheoryGrammar.Par` states it; nothing about lists
  appears in it.

  A complete enumeration of the cuts is one WITNESS for that statement,
  and `Decidable.Enumerated.enum→⊗EM` is the generic bridge.  So this
  file is the whole external residue of CYK at spans, and it is two
  primitives:

      spanEnum  -- `allCuts` / `allCutsComplete`, an induction on ℕ
      spanDecAt -- combine two slot decisions at ONE cut (arity is finite)

  Everything downstream sees only `probe-⊗ᶜ`, which is a term.  This is
  the same discipline as `Strings.Examples.decEqS`: external decidability
  may enter to BUILD an internal map, once, at a named place.

  `probe-⊗ᶜ` is the UNIFORM route, and it is not the one a recursion can
  take: `decAt` decides the two slots independently, and a guarded call
  is available at a slot only once the SIBLING has certified that slot to
  be a proper part.  `Spans.CYK` therefore goes through
  `DecEnum.dec-⊗-cuts`, which asks instead for a decision of each cut AS
  A WHOLE -- weaker, because refuting one slot refutes the cut whatever
  the other slot does.  Both consume the same `allCuts` /
  `allCutsComplete`; only the strength of the per-cut hypothesis differs.
-}
module TheoryGrammar.Instances.Spans.Enumeration where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Par
open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Enumerated

open import TheoryGrammar.Instances.Spans.Graded public

open DecEnum spanFib using (⊗at; Refutes)
open ParS    spanFib using (⊗-EM)

-- ==================================================================
-- PRIMITIVE 2.  Slot decisions combine AT ONE cut.  This is where
-- finiteness of the ARITY is used -- `cat` is binary, so two cases.
-- ==================================================================

spanDecAt : (o : SpanOp) (A : (a : SpanAr o) → SpanG)
            (s : Span) (c : SpanSplit o s)
          → ((a : SpanAr o) → Dec⟨ A a ⟩ (SpanParts o s c a))
          → ⊗at o A s c ⊎ Refutes o A s c
spanDecAt cat A s c h with h true
... | inr k = inr λ g → k (g true)
... | inl x with h false
...   | inr k = inr λ g → k (g false)
...   | inl y = inl λ { true → x ; false → y }

-- ==================================================================
-- The two primitives, bundled.  `allCuts` / `allCutsComplete` are from
-- `Spans.Base`; this is the only place they are consumed.
-- ==================================================================

spanDecEnum : DecEnumerable spanFib ℓ-zero
spanDecEnum .enumSplit    cat (i , n)   = allCuts n
spanDecEnum .enumComplete cat (i , n) c = allCutsComplete n c
spanDecEnum .decAt                      = spanDecAt

-- ==================================================================
-- ... and from here on, TERMS.
--
-- `enum→⊗EM` is the generic bridge from a complete enumeration to the
-- internal statement.  Below it, nothing mentions a cut.
-- ==================================================================

⊗ᶜ-EM : (A B : SpanG) → Probe A → Probe B → ⊗-EM cat (λ b → if b then A else B)
⊗ᶜ-EM A B pa pb =
  enum→⊗EM spanDecEnum cat (λ b → if b then A else B)
           λ s c → λ { true → pa _ tt ; false → pb _ tt }

-- THE MISSING MEMBER OF THE PROBE FAMILY.  `probe-⊕`, `probe-&` and
-- `probe-map` are generic (`TheoryGrammar.View`); `probe-⊗` is the one
-- that cannot be, because deciding a tensor eliminates a sum at a SLOT
-- and concludes at the WHOLE.  At spans it exists, and it is a term.
probe-⊗ᶜ : (A B : SpanG) → Probe A → Probe B → Probe (A ⊗ᶜ B)
probe-⊗ᶜ A B pa pb = ⊗ᶜ-EM A B pa pb

-- Sanity: the probe family is now closed under every connective the
-- span theory has -- `⊕`, `&` and `⊗ᶜ` -- so a decision procedure over
-- spans is a composite of combinators and nothing else.
private
  _ : (A B C : SpanG) → Probe A → Probe B → Probe C
    → Probe ((A ⊗ᶜ B) ⊕ C)
  _ = λ A B C pa pb pc → probe-⊕ (A ⊗ᶜ B) C (probe-⊗ᶜ A B pa pb) pc
