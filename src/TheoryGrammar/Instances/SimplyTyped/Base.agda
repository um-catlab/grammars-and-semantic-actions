{-
  The connectives of the three-sorted theory: one tensor per operation,
  now spread over two result sorts, plus the generic combinator,
  decision and distributivity layers in one `open`.

  `AnnG` is the new shape: a `tm` slot and a `ty` slot, so like `LamG`
  it cannot be written with `if_then_else_`.  `BaseG` is the tensor at
  the EMPTY arity.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Decidable
open import TheoryGrammar.Distributive
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered

module StBase (Name : Type₀) where

  open Terms Name public
  open DecFib stlcFib public
  open Dist (stlcFib .carrier) public
    using (⊕ᴰ-map; ⊕ᴰ-swap; ⊕ᴰ-⊕-out; ⊕ᴰ-⊕-in;
           ⊕ᴰ-&-out; ⊕ᴰ-&-in; dist&r; dist&₂)

  TmG : Type₁
  TmG = TheoryTy ℓ-zero tm          -- Raw  → Type

  NmG : Type₁
  NmG = TheoryTy ℓ-zero nm          -- Name → Type

  TyG : Type₁
  TyG = TheoryTy ℓ-zero ty          -- Ty   → Type

  -- the representable at sort `nm`, with the sort pinned
  Nm : Name → NmG
  Nm n = ⌈_⌉ {s = nm} n

  -- The slot families are NAMED, one per operation.  Anonymous
  -- `λ { true → _ ; false → _ }` families are indistinguishable to the
  -- unifier once the slot is abstract, and every generic rule (`⊗ˢ-E`,
  -- `⊗ˢ-map`, `⊗-merge`) has the family as an implicit argument.
  varFam : NmG → (a : TAr varOp) → TheoryTy ℓ-zero (TSortOf varOp a)
  varFam P _ = P

  appFam : TmG → TmG → (a : TAr appOp) → TheoryTy ℓ-zero (TSortOf appOp a)
  appFam A B b = if b then A else B

  lamFam : NmG → TmG → (a : TAr lamOp) → TheoryTy ℓ-zero (TSortOf lamOp a)
  lamFam P A true  = P
  lamFam P A false = A

  annFam : TmG → TyG → (a : TAr annOp) → TheoryTy ℓ-zero (TSortOf annOp a)
  annFam A Q true  = A
  annFam A Q false = Q

  arrFam : TyG → TyG → (a : TAr arrOp) → TheoryTy ℓ-zero (TSortOf arrOp a)
  arrFam P Q b = if b then P else Q

  VarG : NmG → TmG
  VarG P = ⊗ˢ varOp (varFam P)

  AppG : TmG → TmG → TmG
  AppG A B = ⊗ˢ appOp (appFam A B)

  LamG : NmG → TmG → TmG
  LamG P A = ⊗ˢ lamOp (lamFam P A)

  AnnG : TmG → TyG → TmG
  AnnG A Q = ⊗ˢ annOp (annFam A Q)

  ArrG : TyG → TyG → TyG
  ArrG P Q = ⊗ˢ arrOp (arrFam P Q)

  -- The representable at sort `ty`, and the same read as a CONSTANT of
  -- any other sort.  `TyEq A B` is `⌈ B ⌉ A`: it is the calculus'
  -- equality of types, not a metalanguage one, and it is the only way
  -- the `ty` sort ever appears inside a `tm`-sorted statement.
  TyEq : Ty → Ty → Type₀
  TyEq A B = ⌈_⌉ {s = ty} B A

  Kty : {s : TSort} → Ty → Ty → TheoryTy ℓ-zero s
  Kty A B _ = TyEq A B

  -- (`dni` and `dec-¬` now live upstream in `Decidable.Additive`,
  --  where they belong: neither mentions the operations.)
