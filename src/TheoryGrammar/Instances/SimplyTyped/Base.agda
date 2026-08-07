{-
  The connectives of the three-sorted theory: one abbreviation per
  TERM-forming operation, plus the generic combinator, decision and
  distributivity layers in one `open`.

  `AnnG` is the new shape -- a `tm` slot and a `ty` slot -- so like
  `LamG` it cannot be written with `if_then_else_`.

  The two `ty`-sorted operations get NO abbreviation, and that is a
  measurement rather than an omission: `baseOp` and `arrOp` are only
  ever consumed generically, as `⊗ˢ o (λ _ → ⊤G)` by the partition
  (`Readable`) and as `⊗ˢ o (λ a → ⌈ m⃗ a ⌉)` by the representable iso
  (`Types`).  The third sort cost this layer nothing.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Distributive
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered

module StBase (Name : Type₀) where

  open Terms Name public
  -- the connectives, the additive rules, the decision layer and the
  -- semantic actions, in one `open`.  `dni` and `dec-¬` arrive from
  -- here too: they were carved out of this instance into
  -- `Decidable.Additive`, where they belong -- neither mentions the
  -- operations.
  open DecFib stlcFib public
  open Dist (stlcFib .carrier) public
    using (⊕ᴰ-map; ⊕ᴰ-⊕-out; ⊕ᴰ-⊕-in; ⊕ᴰ-&-in; dist&r; dist&₂)

  -- A grammar at sort `s` denotes a PREDICATE on the worlds of that
  -- sort -- the derivations it admits, indexed by the thing derived.
  TmG : Type₁
  TmG = TheoryTy ℓ-zero tm          -- Raw  → Type

  NmG : Type₁
  NmG = TheoryTy ℓ-zero nm          -- Name → Type

  TyG : Type₁
  TyG = TheoryTy ℓ-zero ty          -- Ty   → Type

  -- `Nm n` denotes "the name I am looking at is `n`": the representable
  -- at sort `nm`, with the sort pinned.
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

  -- `<Op>G A⃗` denotes "the term I am looking at is an `<op>` node, and
  -- its slots satisfy `A⃗`".  One abbreviation per term-forming
  -- operation; each is `⊗ˢ` at the named slot family.
  VarG : NmG → TmG
  VarG P = ⊗ˢ varOp (varFam P)

  AppG : TmG → TmG → TmG
  AppG A B = ⊗ˢ appOp (appFam A B)

  LamG : NmG → TmG → TmG
  LamG P A = ⊗ˢ lamOp (lamFam P A)

  AnnG : TmG → TyG → TmG
  AnnG A Q = ⊗ˢ annOp (annFam A Q)

  -- `TyEq A B` denotes "`A` is the type `B`" -- the representable at
  -- sort `ty`, read at `A`.  It is the calculus' own equality of types,
  -- not a metalanguage one, and its substitution principle is `⌈⌉-E`.
  TyEq : Ty → Ty → Type₀
  TyEq A B = ⌈_⌉ {s = ty} B A

  -- `Kty A B` denotes the same statement carried as a CONSTANT grammar
  -- at any sort: every world of sort `s` is decorated with `TyEq A B`
  -- and nothing else.  This is the only way the `ty` sort ever appears
  -- inside a `tm`-sorted statement -- `synUnique`'s conclusion is a
  -- `Kty`, which is what makes it a map of the calculus.
  Kty : {s : TSort} → Ty → Ty → TheoryTy ℓ-zero s
  Kty A B _ = TyEq A B
