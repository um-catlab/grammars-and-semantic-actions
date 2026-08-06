{-
  A GENUINELY PARTIAL THEORY: 𝔽₃ WITH INVERSION.

  `Fibered` already IS the notion of a partial algebra -- `Split o m`
  lists the decompositions of `m` and nothing forces a tuple to compose.
  A field is the smallest natural theory that needs this: `inv` is
  undefined at 0.  Here that is not a side condition, it is

      Split invOp f0  =  ⊥.

  Carrier 𝔽₃ = {f0,f1,f2}: `inv` is then the identity on the nonzero
  part, so every table reduces and the tests are `refl`.

  PRIMITIVE (matching the representation): `_+𝔽_`, `_·𝔽_`, `inv`, `Nz`,
  `IsZero`, `IsUnit`, `FldSplit`, `FldParts`.  Nothing else in
  `Instances/Field/` may match on 𝔽.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓ₂ ℓX ℓP : Level

-- ==================================================================
-- Slots.  A two-element arity type of its own, so `parts` is a match
-- on the SLOT and no `Bool` leaks into a statement.
-- ==================================================================

data Slot : Type₀ where
  lhs rhs : Slot

-- ==================================================================
-- The carrier and its tables.  PRIMITIVE.
-- ==================================================================

data 𝔽 : Type₀ where
  f0 f1 f2 : 𝔽

infixl 6 _+𝔽_
infixl 7 _·𝔽_

_+𝔽_ : 𝔽 → 𝔽 → 𝔽                        -- PRIMITIVE
f0 +𝔽 y  = y
f1 +𝔽 f0 = f1
f1 +𝔽 f1 = f2
f1 +𝔽 f2 = f0
f2 +𝔽 f0 = f2
f2 +𝔽 f1 = f0
f2 +𝔽 f2 = f1

_·𝔽_ : 𝔽 → 𝔽 → 𝔽                        -- PRIMITIVE
f0 ·𝔽 y  = f0
f1 ·𝔽 y  = y
f2 ·𝔽 f0 = f0
f2 ·𝔽 f1 = f2
f2 ·𝔽 f2 = f1

-- Recursive predicates, as in `Ring/Base`: every case split happens on
-- the element itself, so they compute.
IsZero : 𝔽 → Type₀                       -- PRIMITIVE
IsZero f0 = Unit
IsZero f1 = ⊥
IsZero f2 = ⊥

IsUnit : 𝔽 → Type₀                       -- PRIMITIVE
IsUnit f0 = ⊥
IsUnit f1 = Unit
IsUnit f2 = ⊥

-- THE DOMAIN OF `inv`, as a type family.  This one predicate is the
-- whole of the partiality.
Nz : 𝔽 → Type₀                           -- PRIMITIVE
Nz f0 = ⊥
Nz f1 = Unit
Nz f2 = Unit

-- ... and `inv` is a DEPENDENT function: it cannot even be stated
-- without its domain.
inv : (m : 𝔽) → Nz m → 𝔽                -- PRIMITIVE
inv f0 ()
inv f1 _ = f1
inv f2 _ = f2

-- the two facts about `inv` the rest of the directory uses
inv-nz : (m : 𝔽) (n : Nz m) → Nz (inv m n)
inv-nz f0 ()
inv-nz f1 _ = tt
inv-nz f2 _ = tt

inv-fix : (m : 𝔽) (n : Nz m) → inv m n Eq.≡ m
inv-fix f0 ()
inv-fix f1 _ = Eq.refl
inv-fix f2 _ = Eq.refl

-- nonzero refutes zero, in `Eq`
nz-not-f0 : (m : 𝔽) → Nz m → m Eq.≡ f0 → ⊥
nz-not-f0 f0 ()
nz-not-f0 f1 _ ()
nz-not-f0 f2 _ ()

nz-transport : {a b : 𝔽} → a Eq.≡ b → Nz a → Nz b
nz-transport Eq.refl n = n

-- ==================================================================
-- The signature: four ring operations and one PARTIAL one.
-- ==================================================================

data FldOp : Type₀ where
  zeroOp addOp oneOp mulOp invOp : FldOp

FldAr : FldOp → Type₀
FldAr zeroOp = ⊥
FldAr addOp  = Slot
FldAr oneOp  = ⊥
FldAr mulOp  = Slot
FldAr invOp  = Unit

fldSig : SortedSig Unit ℓ-zero ℓ-zero
fldSig .ops          = FldOp
fldSig .arities      = FldAr
fldSig .sortOf _ _   = tt
fldSig .resultSort _ = tt

-- ==================================================================
-- The splittings.  `Split invOp m` is "m is somebody's inverse", which
-- in a field is exactly "m ≠ 0"; it is EMPTY at f0, and that emptiness
-- is the only trace partiality leaves.
-- ==================================================================

FldSplit : (o : FldOp) → 𝔽 → Type₀       -- PRIMITIVE
FldSplit zeroOp m = IsZero m
FldSplit addOp  m = Σ[ x ∈ 𝔽 ] Σ[ y ∈ 𝔽 ] (x +𝔽 y Eq.≡ m)
FldSplit oneOp  m = IsUnit m
FldSplit mulOp  m = Σ[ x ∈ 𝔽 ] Σ[ y ∈ 𝔽 ] (x ·𝔽 y Eq.≡ m)
FldSplit invOp  m = Nz m

FldParts : (o : FldOp) (m : 𝔽) → FldSplit o m → FldAr o → 𝔽   -- PRIMITIVE
FldParts zeroOp m sp ()
FldParts addOp  m (x , y , _) lhs = x
FldParts addOp  m (x , y , _) rhs = y
FldParts oneOp  m sp ()
FldParts mulOp  m (x , y , _) lhs = x
FldParts mulOp  m (x , y , _) rhs = y
FldParts invOp  m sp _ = inv m sp

fldFib : Fibered fldSig ℓ-zero ℓ-zero
fldFib .carrier _ = 𝔽
fldFib .Split     = FldSplit
fldFib .parts     = FldParts

-- ==================================================================
-- RESTRICTION ALONG AN INJECTION OF OPERATIONS.  A promodel for a
-- signature is one for any sub-signature, by composition -- no data is
-- invented, so `Split` and `parts` are literally reused.  This is what
-- makes "the ring fragment has a total point, the field does not" a
-- statement about ONE promodel rather than two unrelated ones.
-- ==================================================================

module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') {O : Type ℓ₂} (ι : O → σ .ops) where

  restrictSig : SortedSig S ℓ₂ ℓ'
  restrictSig .ops          = O
  restrictSig .arities o    = σ .arities (ι o)
  restrictSig .sortOf o a   = σ .sortOf (ι o) a
  restrictSig .resultSort o = σ .resultSort (ι o)

  restrictFib : Fibered σ ℓX ℓP → Fibered restrictSig ℓX ℓP
  restrictFib Fib .carrier  = Fib .carrier
  restrictFib Fib .Split o  = Fib .Split (ι o)
  restrictFib Fib .parts o  = Fib .parts (ι o)

-- ==================================================================
-- The ring fragment: the same promodel, four operations.
-- ==================================================================

data RngOp : Type₀ where
  zeroR addR oneR mulR : RngOp

ιR : RngOp → FldOp
ιR zeroR = zeroOp
ιR addR  = addOp
ιR oneR  = oneOp
ιR mulR  = mulOp

rngSig : SortedSig Unit ℓ-zero ℓ-zero
rngSig = restrictSig fldSig ιR

rngFib : Fibered rngSig ℓ-zero ℓ-zero
rngFib = restrictFib fldSig ιR fldFib

-- THE FRAGMENT IS TOTAL.  (𝔽₃,0,+,1,·) is an honest algebra.
rngPoint : LaxPoint rngFib
rngPoint .op zeroR _ = f0
rngPoint .op addR  h = h lhs +𝔽 h rhs
rngPoint .op oneR  _ = f1
rngPoint .op mulR  h = h lhs ·𝔽 h rhs
rngPoint .split zeroR h = tt
rngPoint .split addR  h = h lhs , h rhs , Eq.refl
rngPoint .split oneR  h = tt
rngPoint .split mulR  h = h lhs , h rhs , Eq.refl
rngPoint .parts-split zeroR h = funExt λ ()
rngPoint .parts-split addR  h = funExt λ { lhs → refl ; rhs → refl }
rngPoint .parts-split oneR  h = funExt λ ()
rngPoint .parts-split mulR  h = funExt λ { lhs → refl ; rhs → refl }

-- ... and honest: every splitting really does recompose.
rngHonest : Honest rngPoint
rngHonest zeroR f0 tt = Eq.refl
rngHonest addR  m (x , y , e) = e
rngHonest oneR  f1 tt = Eq.refl
rngHonest mulR  m (x , y , e) = e
