{- The connectives of the three-sorted linear theory: one abbreviation per
   TERM-forming operation, plus the generic combinator, decision and
   distributivity layers in one `open`. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat using (ℕ)

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Distributive
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered

-- the connectives, the additive rules, the decision layer and the
-- semantic actions, in one `open`
open DecFib linFib public
open Dist (linFib .carrier) public
  using (⊕ᴰ-map; ⊕ᴰ-⊕-out; ⊕ᴰ-⊕-in; ⊕ᴰ-&-in; ⊕ᴰ-swap; dist&r; dist&₂)

-- A grammar at sort `s` denotes a PREDICATE on the worlds of that sort
-- -- the derivations it admits, indexed by the thing derived.
TmG : Type₁
TmG = TheoryTy ℓ-zero tm          -- Raw → Type

NmG : Type₁
NmG = TheoryTy ℓ-zero nm          -- ℕ   → Type

TyG : Type₁
TyG = TheoryTy ℓ-zero ty          -- Ty  → Type

-- `Nm n` denotes "the index I am looking at is `n`": the representable
-- at sort `nm`, with the sort pinned.
Nm : ℕ → NmG
Nm n = ⌈_⌉ {s = nm} n

-- The slot families are NAMED, one per operation.
varFam : NmG → (a : TAr varOp) → TheoryTy ℓ-zero (TSortOf varOp a)
varFam P _ = P

appFam : TmG → TmG → (a : TAr appOp) → TheoryTy ℓ-zero (TSortOf appOp a)
appFam A B b = if b then A else B

lamFam : TmG → (a : TAr lamOp) → TheoryTy ℓ-zero (TSortOf lamOp a)
lamFam A _ = A

annFam : TmG → TyG → (a : TAr annOp) → TheoryTy ℓ-zero (TSortOf annOp a)
annFam A Q true  = A
annFam A Q false = Q

-- `<Op>G A⃗` denotes "the term I am looking at is an `<op>` node, and
-- its slots satisfy `A⃗`".
VarG : NmG → TmG
VarG P = ⊗ˢ varOp (varFam P)

AppG : TmG → TmG → TmG
AppG A B = ⊗ˢ appOp (appFam A B)

LamG : TmG → TmG
LamG A = ⊗ˢ lamOp (lamFam A)

AnnG : TmG → TyG → TmG
AnnG A Q = ⊗ˢ annOp (annFam A Q)

-- `TyEq A B` denotes "`A` is the type `B`" -- the representable at sort
-- `ty`, read at `A`.  It is the calculus' own equality of types, not a
-- metalanguage one, and its substitution principle is `⌈⌉-E`.
TyEq : Ty → Ty → Type₀
TyEq A B = ⌈_⌉ {s = ty} B A

-- `Kty A B` denotes the same statement carried as a CONSTANT grammar at
-- any sort.  This is the only way the `ty` sort ever appears inside a
-- `tm`-sorted statement -- `synUnique`'s conclusion is a `Kty`.
Kty : {s : TSort} → Ty → Ty → TheoryTy ℓ-zero s
Kty A B _ = TyEq A B
