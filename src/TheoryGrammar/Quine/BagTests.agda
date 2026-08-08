{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE BAG QUINES, RUN. Every `refl` below is the decision procedure
   filling its chart at typecheck time -- searching `2ⁿ` PARTITIONS of the
   bag rather than a string's `n+1` cuts -- and the interpreter running on
   whichever parse tree that search produced. -}
module TheoryGrammar.Quine.BagTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Bag

-- §0  THE SOURCE.  Written ONCE.  Two elements -- half the length of
--     `Quine.Tiny`'s `0#00`, because quoting costs alphabet here and
--     not length, and because the separator costs nothing at all.

src : Bag
src = k0 ∷ q0 ∷ []

-- §1  IT PARSES -- and the parse tree is a THEOREM, not a report.

_ : passes (run (derives! ntS) at (src ↦ true ∷ []))
_ = refl

selfDeriv : Deriv ntS src
selfDeriv = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) src refl

-- `⌈_⌉` PINS the text: `⌈ src ⌉` holds at one world and that world IS
-- the source, so this term says "the source, and nothing else, derives
-- from S".
selfLit : ⌈ src ⌉ ⊢ Deriv ntS
selfLit = ⌈⌉-E selfDeriv

-- §2 ... AND IT PRINTS ITSELF.

quine : (interp ntS ∘g selfLit) src (⌈⌉-pt src) ≡ (count src , tt)
quine = refl

-- the same fact through the whole pipeline -- decide, then interpret --
-- printed back as a text by `canon`
_ : passes (runOutBag at (src ↦ just src ∷ []))
_ = refl

-- §3 ONE QUINE, MANY TEXTS. This is what the bag theory buys.

srcSwap : Bag
srcSwap = q0 ∷ k0 ∷ []

_ : passes (run (derives! ntS) at (srcSwap ↦ true ∷ []))
_ = refl

swapDeriv : Deriv ntS srcSwap
swapDeriv = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) srcSwap refl

-- THE CLASS-LEVEL QUINE EQUATION: the OTHER text of the class prints
-- the SAME multiset, namely `count src`.  (`count srcSwap` is `count
-- src` on the nose; both sides are literals.)
quine-swap : (interp ntS ∘g ⌈⌉-E swapDeriv) srcSwap (⌈⌉-pt srcSwap)
           ≡ (count src , tt)
quine-swap = refl

-- ... and the printer, from either text, gives the class's canonical
-- representative
_ : passes (runOutBag at (src ↦ just src ∷ srcSwap ↦ just src ∷ []))
_ = refl

-- §4 THE OPCODE THAT HAS NO STRING QUINES HAS BAG QUINES.

src1 : Bag
src1 = k1 ∷ q1 ∷ []

_ : passes (run (derives! ntS) at (src1 ↦ true ∷ []))
_ = refl

deriv1 : Deriv ntS src1
deriv1 = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) src1 refl

quine1 : (interp ntS ∘g ⌈⌉-E deriv1) src1 (⌈⌉-pt src1) ≡ (count src1 , tt)
quine1 = refl

_ : passes (runOutBag at (src1 ↦ just src1 ∷ []))
_ = refl

-- §5 A FOUR-ELEMENT QUINE, AND ITS CLASS. `k0 k1 q0 q1`: code counts
-- `(1,1)`, data counts `(1,1)`, opcode `1`.

src4 : Bag
src4 = k0 ∷ k1 ∷ q0 ∷ q1 ∷ []

deriv4 : Deriv ntS src4
deriv4 = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) src4 refl

quine4 : (interp ntS ∘g ⌈⌉-E deriv4) src4 (⌈⌉-pt src4) ≡ (count src4 , tt)
quine4 = refl

_ : passes (runOutBag at
             ( src4                        ↦ just src4
             ∷ (q1 ∷ q0 ∷ k1 ∷ k0 ∷ [])    ↦ just src4
             ∷ (k1 ∷ q0 ∷ k0 ∷ q1 ∷ [])    ↦ just src4
             ∷ [] ))
_ = refl

-- ... and the OTHER opcode's four-element member, `k0 k0 q0 q0` (`quine-0`
-- at `a = 2`).
src4' : Bag
src4' = k0 ∷ k0 ∷ q0 ∷ q0 ∷ []

deriv4' : Deriv ntS src4'
deriv4' = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) src4' refl

quine4' : (interp ntS ∘g ⌈⌉-E deriv4') src4' (⌈⌉-pt src4') ≡ (count src4' , tt)
quine4' = refl

_ : passes (runOutBag at (src4' ↦ just src4' ∷ []))
_ = refl

-- §6  THE PROPERTY IS NOT FREE.  Neighbours, and what they print.

-- `k0 q1`: the code says `0` but the data says `1`.  Opcode 0, data
-- `(0,1)`, so it prints the OTHER quine.
_ : passes (runOutBag at ((k0 ∷ q1 ∷ []) ↦ just (k1 ∷ q1 ∷ []) ∷ []))
_ = refl

-- `k1 q0`: the mirror image -- opcode 1, data `(1,0)`, so it prints the
-- FIRST quine.  Neither of these two is a fixed point, and each prints
-- the other one's fixed point.
_ : passes (runOutBag at ((k1 ∷ q0 ∷ []) ↦ just (k0 ∷ q0 ∷ []) ∷ []))
_ = refl

-- `k0 k0 q0`: the code is twice as long as the data.
_ : passes (runOutBag at ((k0 ∷ k0 ∷ q0 ∷ []) ↦ just (k0 ∷ q0 ∷ []) ∷ []))
_ = refl

-- `k1 k1 q0 q0`: opcode 2 -- the instruction that quotes TWICE.  It
-- grows, and `no-quine-2+` says it always does: no opcode-2 program is
-- ever a fixed point, and the reason is `a + a ≡ a`.
_ : passes (runOutBag at
             ( (k1 ∷ k1 ∷ q0 ∷ q0 ∷ [])
               ↦ just (k0 ∷ k0 ∷ q0 ∷ q0 ∷ q0 ∷ q0 ∷ []) ∷ []))
_ = refl

-- §7  AND THE LANGUAGE IS NOT EVERYTHING.  A negative answer here is a
--     REFUTATION (the error grammar is `¬G _`), so these are theorems
--     that no parse tree exists -- not reports that none was found.

_ : passes (run (derives! ntS) at
             ( (k0 ∷ [])                ↦ false   -- code, but no data
             ∷ (q0 ∷ [])                ↦ false   -- data, but no code
             ∷ []                       ↦ false   -- nothing at all
             ∷ (k0 ∷ k1 ∷ [])           ↦ false   -- all code
             ∷ (q0 ∷ q1 ∷ [])           ↦ false   -- all data
             ∷ [] ))
_ = refl

noDeriv : (w : Bag) → run (derives! ntS) w ≡ false → (¬G Deriv ntS) w
noDeriv = refute (Deriv ntS) (¬G Deriv ntS) (derives? ntS)

-- a bag of code letters alone is NOT a program, and this is a proof
no-code-only : Deriv ntS (k0 ∷ k1 ∷ []) → E.⊥* {ℓ-zero}
no-code-only = noDeriv (k0 ∷ k1 ∷ []) refl

-- ... and neither is a bag of data letters alone.  Note there is no
-- ORDER hypothesis in either statement: at bags "the code comes first"
-- is not a thing that could have been assumed.
no-data-only : Deriv ntS (q0 ∷ q1 ∷ []) → E.⊥* {ℓ-zero}
no-data-only = noDeriv (q0 ∷ q1 ∷ []) refl
