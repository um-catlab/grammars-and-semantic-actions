{-
  PROMODEL: the abstract description, and its equivalence to the
  concrete one.

  You called it right -- "promonoidal" is the monoid instance of this.
  Generic in a theory, the structure is a PROMODEL: a model of the
  signature in which each operation is interpreted not as a function but
  as a PROFUNCTOR.  Since the base is discrete, a profunctor
  `(∏_a carrier (sortOf o a))^op × carrier (resultSort o) → Set` is just
  a proof-relevant relation, which is why everything computes: the Day
  coend degenerates to a Σ.

      Model     : operations are functions
      PointedProModel  : operations are profunctors, containing their graphs

  The `graph` field is the only content beyond the bare relation, and it
  replaces `Fibered`'s two fields `split` and `parts-split` with one:
  an element of `Rel o m⃗ (op o m⃗)` IS a splitting of `op o m⃗` together
  with a proof its parts are `m⃗`.

  `Fibered` is then the same data destructured the other way -- Split
  indexed by the output, parts as a projection -- and `splitIso` /
  `relIso` below check that the two presentations recover each other.
  Both round trips are `refl` once the mediating equality is `Eq.≡`
  rather than a path, which is also why neither direction transports.

  Bags is the instance that shows the relation must be allowed to be
  STRICTLY LARGER than the graph: `Ilv u v w` does not imply
  `u ++ v ≡ w`.  So `graph` is a containment, never an isomorphism, and
  a soundness field `op-parts` would wrongly rule that out.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.PointedProModel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓX ℓP ℓR : Level

-- ==================================================================
-- The abstract description.
-- ==================================================================

record PointedProModel {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX ℓR
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓR))))) where
  field
    carrier : S → Type ℓX
    op      : (o : σ .ops)
            → ((a : σ .arities o) → carrier (σ .sortOf o a))
            → carrier (σ .resultSort o)
    -- each operation ALSO as a profunctor (discrete base ⇒ a relation)
    Rel     : (o : σ .ops)
            → ((a : σ .arities o) → carrier (σ .sortOf o a))
            → carrier (σ .resultSort o) → Type ℓR
    -- ... which contains the operation's graph
    graph   : (o : σ .ops)
              (m⃗ : (a : σ .arities o) → carrier (σ .sortOf o a))
            → Rel o m⃗ (op o m⃗)

open PointedProModel public

-- ==================================================================
-- The two presentations translate.
-- ==================================================================

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  fromPro : PointedProModel σ ℓX ℓR → Fibered σ ℓX (ℓ-max (ℓ-max ℓ' ℓX) ℓR)
  fromPro P .Fibered.carrier = P .carrier
  fromPro P .Fibered.Split o m =
    Σ[ m⃗ ∈ ((a : σ .arities o) → P .carrier (σ .sortOf o a)) ] P .Rel o m⃗ m
  fromPro P .Fibered.parts o m (m⃗ , _) = m⃗

  -- the point travels separately now, which is the whole content of the
  -- split: `PointedProModel`'s `op`/`graph` ARE a `LaxPoint`, and the
  -- bare relation is what survives without them.
  fromProPoint : (P : PointedProModel σ ℓX ℓR) → LaxPoint (fromPro P)
  fromProPoint P .op = P .op
  fromProPoint P .split o m⃗ = m⃗ , P .graph o m⃗
  fromProPoint P .parts-split o m⃗ = refl

  toPro : (Fib : Fibered σ ℓX ℓP) → LaxPoint Fib
        → PointedProModel σ ℓX (ℓ-max (ℓ-max ℓ' ℓX) ℓP)
  toPro Fib Q .carrier = Fib .Fibered.carrier
  toPro Fib Q .op      = Q .op
  toPro Fib Q .Rel o m⃗ m =
    Σ[ sp ∈ Fib .Fibered.Split o m ] (Fib .Fibered.parts o m sp Eq.≡ m⃗)
  toPro Fib Q .graph o m⃗ =
    Q .split o m⃗ , Eq.pathToEq (Q .parts-split o m⃗)

  -- ================================================================
  -- ... and the round trips recover the data, both by refl.
  -- ================================================================

  splitIso : (Fib : Fibered σ ℓX ℓP) (Q : LaxPoint Fib) (o : σ .ops)
             (m : Fib .Fibered.carrier (σ .resultSort o))
           → Iso (Fibered.Split (fromPro (toPro Fib Q)) o m)
                 (Fib .Fibered.Split o m)
  splitIso Fib Q o m .Iso.fun (m⃗ , sp , Eq.refl) = sp
  splitIso Fib Q o m .Iso.inv sp = Fib .Fibered.parts o m sp , sp , Eq.refl
  splitIso Fib Q o m .Iso.sec sp = refl
  splitIso Fib Q o m .Iso.ret (m⃗ , sp , Eq.refl) = refl

  relIso : (P : PointedProModel σ ℓX ℓR) (o : σ .ops)
           (m⃗ : (a : σ .arities o) → P .carrier (σ .sortOf o a))
           (m : P .carrier (σ .resultSort o))
         → Iso (Rel (toPro (fromPro P) (fromProPoint P)) o m⃗ m) (P .Rel o m⃗ m)
  relIso P o m⃗ m .Iso.fun ((m⃗' , r) , Eq.refl) = r
  relIso P o m⃗ m .Iso.inv r = (m⃗ , r) , Eq.refl
  relIso P o m⃗ m .Iso.sec r = refl
  relIso P o m⃗ m .Iso.ret ((m⃗' , r) , Eq.refl) = refl
