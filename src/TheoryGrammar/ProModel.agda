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
      ProModel  : operations are profunctors, containing their graphs

  The `graph` field is the only content beyond the bare relation, and it
  replaces `Substrate`'s two fields `split` and `parts-split` with one:
  an element of `Rel o m⃗ (op o m⃗)` IS a splitting of `op o m⃗` together
  with a proof its parts are `m⃗`.

  `Substrate` is then the same data destructured the other way -- Split
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
module TheoryGrammar.ProModel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate

private variable ℓS ℓ ℓ' ℓX ℓP ℓR : Level

-- ==================================================================
-- The abstract description.
-- ==================================================================

record ProModel {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX ℓR
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

open ProModel public

-- ==================================================================
-- The two presentations translate.
-- ==================================================================

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  toSub : ProModel σ ℓX ℓR → Substrate σ ℓX (ℓ-max (ℓ-max ℓ' ℓX) ℓR)
  toSub P .Substrate.carrier = P .carrier
  toSub P .Substrate.op      = P .op
  toSub P .Substrate.Split o m =
    Σ[ m⃗ ∈ ((a : σ .arities o) → P .carrier (σ .sortOf o a)) ] P .Rel o m⃗ m
  toSub P .Substrate.parts o m (m⃗ , _) = m⃗
  toSub P .Substrate.split o m⃗ = m⃗ , P .graph o m⃗
  toSub P .Substrate.parts-split o m⃗ = refl

  fromSub : Substrate σ ℓX ℓP → ProModel σ ℓX (ℓ-max (ℓ-max ℓ' ℓX) ℓP)
  fromSub Sub .carrier = Sub .Substrate.carrier
  fromSub Sub .op      = Sub .Substrate.op
  fromSub Sub .Rel o m⃗ m =
    Σ[ sp ∈ Sub .Substrate.Split o m ] (Sub .Substrate.parts o m sp Eq.≡ m⃗)
  fromSub Sub .graph o m⃗ =
    Sub .Substrate.split o m⃗ , Eq.pathToEq (Sub .Substrate.parts-split o m⃗)

  -- ================================================================
  -- ... and the round trips recover the data, both by refl.
  -- ================================================================

  splitIso : (Sub : Substrate σ ℓX ℓP) (o : σ .ops)
             (m : Sub .Substrate.carrier (σ .resultSort o))
           → Iso (Substrate.Split (toSub (fromSub Sub)) o m)
                 (Sub .Substrate.Split o m)
  splitIso Sub o m .Iso.fun (m⃗ , sp , Eq.refl) = sp
  splitIso Sub o m .Iso.inv sp = Sub .Substrate.parts o m sp , sp , Eq.refl
  splitIso Sub o m .Iso.sec sp = refl
  splitIso Sub o m .Iso.ret (m⃗ , sp , Eq.refl) = refl

  relIso : (P : ProModel σ ℓX ℓR) (o : σ .ops)
           (m⃗ : (a : σ .arities o) → P .carrier (σ .sortOf o a))
           (m : P .carrier (σ .resultSort o))
         → Iso (Rel (fromSub (toSub P)) o m⃗ m) (P .Rel o m⃗ m)
  relIso P o m⃗ m .Iso.fun ((m⃗' , r) , Eq.refl) = r
  relIso P o m⃗ m .Iso.inv r = (m⃗ , r) , Eq.refl
  relIso P o m⃗ m .Iso.sec r = refl
  relIso P o m⃗ m .Iso.ret ((m⃗' , r) , Eq.refl) = refl
