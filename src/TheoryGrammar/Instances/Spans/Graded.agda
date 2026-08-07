{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE GRADING ON SPANS -- and with it, the CYK chart.

  `deg (i , n) = n`: a span is measured by its LENGTH, not by where it
  sits.  So `▷ A` at a span is "A at every SHORTER span", which is
  exactly the SHAPE of a CYK chart: every recursive call lands at a
  strictly shorter span, and `löb` supplies that with nothing that isn't
  already in `TheoryGrammar.Graded`.

  Not claimed: the SHARING.  `löb` is `WFI.induction` and re-descends at
  every consultation, so the connective gives the chart's well-founded
  structure but does not tabulate it -- see the measurements in
  `Spans.Examples`.  Cubic CYK would need a tabulated fixpoint, which is
  a different construction.

  Everything mirrors `Instances.Strings.Graded` clause for clause, with
  `Cut` in place of `Split3`; that the two proofs have the same shape is
  the point, since both are instances of one generic interface.
-}
module TheoryGrammar.Instances.Spans.Graded where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Spans.Base public

-- ==================================================================
-- Cuts never grow the length, and shrink it when the complement is
-- non-empty.  Compare `split3LenL` / `split3LenR` / their strict forms.
-- ==================================================================

cutL≤ : {n : ℕ} (c : Cut n) → cutL c ≤ n
cutL≤ here     = zero-≤
cutL≤ (shift c) = suc-≤-suc (cutL≤ c)

cutR≤ : {n : ℕ} (c : Cut n) → cutR c ≤ n
cutR≤ here     = ≤-refl
cutR≤ (shift c) = ≤-suc (cutR≤ c)

cutL< : {n : ℕ} (c : Cut n) → 0 < cutR c → cutL c < n
cutL< here     pr = pr
cutL< (shift c) pr = suc-≤-suc (cutL< c pr)

cutR< : {n : ℕ} (c : Cut n) → 0 < cutL c → cutR c < n
cutR< here     pr = E.rec (¬-<-zero pr)
cutR< (shift c) pr = suc-≤-suc (cutR≤ c)

-- ==================================================================
-- THE RESOURCE PREDICATE, internally: a span is non-empty when it cuts
-- with a UNIT span on the left.  Same shape as `Strings.NonTrivial`
-- (`⌈_⌉`, `⊗`, `⊕ᴰ`, `⊤` only) -- the `⊕ᴰ ℕ` quantifies over the start
-- position exactly as the string version quantifies over the character.
-- ==================================================================

NonEmpty : SpanG
NonEmpty = ⊕ᴰ ℕ (λ j → ⌈ (j , 1) ⌉ ⊗ᶜ ⊤G)

-- PRIMITIVE (phase 1).  The ONE bridge from the internal predicate to
-- the grading, exactly as `Strings.Graded.ntLen`.
neLen : {s : Span} → NonEmpty s → 0 < s .snd
neLen {i , n} (j , c , h) = subst (0 <_) (cut-sum c) lem
  where
    l1 : cutL c ≡ 1
    l1 = cong snd (Eq.eqToPath (h true))

    lem : 0 < cutL c + cutR c
    lem = subst (λ k → 0 < k + cutR c) (sym l1) (suc-≤-suc zero-≤)

-- PRIMITIVE (phase 1).  The converse bridge: a span of positive length
-- IS non-empty.  `neLen` and `mkNE` together are the whole relationship
-- between the internal predicate and the grading, and nothing else in
-- the span instance may look at a length.
mkNE : (s : Span) → 0 < s .snd → NonEmpty s
mkNE (j , zero)  p = E.rec (¬-<-zero p)
mkNE (j , suc k) _ = j , shift here , λ { true → Eq.refl ; false → tt }

-- ... and so non-emptiness is DECIDED, as an internal probe.  This is
-- the resource test the parser branches on; it is `Probe`-typed, so
-- every consumer eliminates it with `dec-elim` and never sees a length.
probe-NE : Probe NonEmpty
probe-NE (j , zero)  _ =
  dec-no NonEmpty (j , zero) λ ne → E.rec (¬-<-zero (neLen ne))
probe-NE (j , suc k) _ =
  dec-yes NonEmpty (j , suc k) (mkNE (j , suc k) (suc-≤-suc zero-≤))

-- ==================================================================
-- The graded structure.
-- ==================================================================

SpanProper : (o : SpanOp) (s : Span) → SpanSplit o s → SpanAr o → Type₀
SpanProper cat (i , n) c b =
  NonEmpty (SpanParts cat (i , n) c (not b))

spanGraded : GradedFib spanSig ℓ-zero ℓ-zero
spanGraded .fib      = spanFib
spanGraded .deg _ s  = s .snd
spanGraded .Proper   = SpanProper
spanGraded .deg≤ cat (i , n) c true  = cutL≤ c
spanGraded .deg≤ cat (i , n) c false = cutR≤ c
spanGraded .deg< cat (i , n) c true  pr = cutL< c (neLen pr)
spanGraded .deg< cat (i , n) c false pr = cutR< c (neLen pr)

-- ▷, löb, the description language and the hylomorphism, at spans.
-- `▷ A (P , (i , n))` unfolds to "A at every span of length < n" --
-- the CYK chart, as a connective.
open Guard spanGraded ℓ-zero Unit (λ _ → tt) public
