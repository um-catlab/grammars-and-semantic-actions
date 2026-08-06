{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE THEORY OF SPANS -- and the first instance with NO POINT.

  CYK does not split strings into strings.  It splits a SPAN into two
  adjacent spans, remembering the ambient word.  That is a different
  algebraic theory, so it gets its own instance rather than being forced
  into `Instances.Strings`.

  One sort, one binary operation: adjacent composition.  The operation is
  PARTIAL -- `(i,j)` and `(k,l)` compose only when `j ≡ k` -- and that is
  the point of the file:

      `Fibered` needs only `carrier`, `Split`, `parts`.
      `LaxPoint` (`op`, `split`, `parts-split`) is what needs totality.

  So spans are a `Fibered` with NO `LaxPoint`, and there is nothing
  missing: every connective, the description language, `▷`/`löb`, and the
  whole decision layer are `RulesF`/`DecFib`, which never consult a
  point.  This is the first instance that could not have been written
  before `Substrate` was split, and it is independent evidence that the
  split was cut in the right place.

  Concretely `parts-split` is what fails: it says every tuple splits its
  own composite AT the tuple you started with, and for a partial
  operation the composite of a non-adjacent pair forgets which pair it
  came from.  `(0,2)·(5,3)` cannot be recovered from anything.

  WHAT THIS BUYS, and what it does not.

  Buys: the CHART.  `deg (i , n) = n`, so `▷ Dec⟨Deriv P⟩` at a span is
  "decided at every SHORTER span" -- which is exactly the filled part of
  a CYK chart.  Memoisation by span length, which is what distinguishes
  CYK from derivative parsing, is `löb` here and needs nothing new.

  Does not buy: the inner cut-scan.  `Split cat (i , n)` is a Type, not a
  sort, in this theory as in every other -- `TheoryTy` is a family over
  the CARRIER -- so there is still no grammar indexed by the cuts of the
  current span, and still no way to iterate them internally.  That stays
  one primitive.  What improves is the primitive's obligation: `Cut n` is
  an inductive family over ℕ with `n+1` elements, so enumerating it is an
  induction on a number rather than on a string.
-}
module TheoryGrammar.Instances.Spans.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable
open import TheoryGrammar.View

-- ==================================================================
-- Signature: one sort, one binary operation (adjacent composition).
-- ==================================================================

data SpanOp : Type₀ where
  cat : SpanOp

SpanAr : SpanOp → Type₀
SpanAr cat = Bool

spanSig : SortedSig Unit ℓ-zero ℓ-zero
spanSig .ops          = SpanOp
spanSig .arities      = SpanAr
spanSig .sortOf _ _   = tt
spanSig .resultSort _ = tt

-- ==================================================================
-- Spans, and their cuts.
-- ==================================================================

-- a span is (start , length)
Span : Type₀
Span = ℕ × ℕ

-- The cuts of a span of length `n`, as an INDUCTIVE family: `here` cuts
-- at the front, `shift` shifts one place right.  `Cut n` has `n+1`
-- elements, and this is the structure the scan recurses on.
data Cut : ℕ → Type₀ where
  here : {n : ℕ} → Cut n
  shift : {n : ℕ} → Cut n → Cut (suc n)

cutL : {n : ℕ} → Cut n → ℕ
cutL here     = 0
cutL (shift c) = suc (cutL c)

cutR : {n : ℕ} → Cut n → ℕ
cutR {n} here = n
cutR (shift c) = cutR c

-- the cut really does split the length
cut-sum : {n : ℕ} (c : Cut n) → cutL c + cutR c ≡ n
cut-sum here     = refl
cut-sum (shift c) = cong suc (cut-sum c)

-- ==================================================================
-- The fibered structure.  NOTE: no `op`, no `split`, no `parts-split`.
-- ==================================================================

SpanSplit : SpanOp → Span → Type₀
SpanSplit cat (i , n) = Cut n

SpanParts : (o : SpanOp) (s : Span) → SpanSplit o s → SpanAr o → Span
SpanParts cat (i , n) c b =
  if b then (i , cutL c) else (i + cutL c , cutR c)

spanFib : Fibered spanSig ℓ-zero ℓ-zero
spanFib .carrier _ = Span
spanFib .Split     = SpanSplit
spanFib .parts     = SpanParts

-- ==================================================================
-- The cuts are finitely enumerable, by induction on the LENGTH.
--
-- This is the residual obligation -- the one thing the calculus cannot
-- do internally, in this theory as in any other.  But compare
-- `Strings.Enumeration.cuts`, which inducts on a string: here it is an
-- induction on ℕ, and `Cut` is the canonical structure rather than a
-- `List` that has to be proved complete separately.
-- ==================================================================

allCuts : (n : ℕ) → List (Cut n)
allCuts zero    = here ∷ []
allCuts (suc n) = here ∷ map shift (allCuts n)

-- ==================================================================
-- SANITY: the whole layer really is available with no point.
--
-- If any of these needed `op`, the file would not typecheck -- so this
-- block IS the evidence for the claim in the header, not a restatement
-- of it.
-- ==================================================================

open DecFib spanFib public
open Views  spanFib public

SpanG : Type₁
SpanG = TheoryTy ℓ-zero tt

-- the concatenation tensor: "this span cuts into an A-span and a B-span"
infixr 21 _⊗ᶜ_
_⊗ᶜ_ : SpanG → SpanG → SpanG
A ⊗ᶜ B = ⊗ˢ cat (λ b → if b then A else B)

private
  -- the additives, the tensor's functorial action, the decision layer
  -- and the view layer, all with no point in sight
  -- (the families must be pinned: an arity-indexed family has no η, so
  -- `if b then A else B` is not recoverable from a metavariable)
  _ : (A B A' B' : SpanG) → A ⊢ A' → B ⊢ B' → (A ⊗ᶜ B) ⊢ (A' ⊗ᶜ B')
  _ = λ A B A' B' f g →
        ⊗ˢ-map cat {A = λ b → if b then A else B}
                   {B = λ b → if b then A' else B'}
                   λ { true → f ; false → g }

  _ : (A : SpanG) → Cover A → Probe A
  _ = cover→probe

  _ : (A B : SpanG) → Probe A → Probe B → Probe (A ⊕ B)
  _ = probe-⊕
