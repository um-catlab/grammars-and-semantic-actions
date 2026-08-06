{-
  IMAGE AND DOMAIN OF AN OPERATION, AS GRAMMARS.

  Generic over any `Fibered`.  Two grammars, at two different sorts:

      Imgˢ o     at  resultSort o   -- `⊗ˢ o ⊤`: m is an o-composite
      Domˢ o i   at  sortOf o i     -- x occurs in slot i of one

  `⊗ˢ o ⊤` is the IMAGE, not the domain: `Covering` (surjectivity of the
  point) is exactly what makes it `⊤` (`covering→img` / `img→covering`),
  and a total nullary operation already fails it.  The DOMAIN is `Domˢ`,
  and a `LaxPoint` forces it to be `⊤` at every FILLABLE slot -- so an
  internal refutation `Domˢ o i ⊢ ¬G ⌈ x ⌉` refutes every total point.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field.Domain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

module DomainOf {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open RulesF Fib public
  open DecAdd (Fib .carrier) public using (¬G_; Dec⟨_⟩; dec-yes; dec-no;
    ⊕-E-at; ⊕-E-atᴰ; dec-elim; Complement; Decision; decide; exclude;
    ¬G-excludes; largest; toDec; contra; &-swap; ¬G-map)

  -- ================================================================
  -- The two grammars.
  -- ================================================================

  -- the IMAGE of o: which results are o-composites at all.  This is
  -- literally `⊗ˢ o ⊤`, named.
  Imgˢ : (o : σ .ops) → TheoryTy (ℓ-max ℓP ℓ') (σ .resultSort o)
  Imgˢ o = ⊗ˢ o (λ _ → ⊤G)

  -- the DOMAIN of o at slot i: which arguments occur in slot i of some
  -- splitting.  Definable from `Split`/`parts` alone -- no point.
  Domˢ : (o : σ .ops) (i : σ .arities o) → TheoryTy (ℓ-max ℓX ℓP) (σ .sortOf o i)
  Domˢ o i x = Σ[ m ∈ Fib .carrier (σ .resultSort o) ]
               Σ[ sp ∈ Fib .Split o m ] (Fib .parts o m sp i Eq.≡ x)

  -- transport of splittings along an `Eq`, so nothing below uses a Path
  -- where the index has to reduce
  splitEq : (o : σ .ops) {m n : Fib .carrier (σ .resultSort o)}
          → m Eq.≡ n → Fib .Split o m → Fib .Split o n
  splitEq o Eq.refl sp = sp

  -- ================================================================
  -- WHAT A TOTAL POINT FORCES.
  -- ================================================================

  -- a way to complete a tuple around slot i.  Trivial for a unary
  -- operation; for a wider one it is "pad the other slots".
  record Fills (o : σ .ops) (i : σ .arities o) : Type (ℓ-max ℓ' ℓX) where
    field
      pad   : Fib .carrier (σ .sortOf o i)
             → (a : σ .arities o) → Fib .carrier (σ .sortOf o a)
      pad-i : (x : Fib .carrier (σ .sortOf o i)) → pad x i ≡ x

  open Fills public

  -- THEOREM.  A total point makes every fillable slot TOTAL: its domain
  -- grammar is ⊤.  (`split` supplies the splitting, `parts-split` says
  -- the slot really holds what you put there.)
  point→dom : (P : LaxPoint Fib) (o : σ .ops) (i : σ .arities o)
            → Fills o i → ⊤G ⊢ Domˢ o i
  point→dom P o i F x _ =
      P .op o (F .pad x)
    , P .split o (F .pad x)
    , Eq.pathToEq (funExt⁻ (P .parts-split o (F .pad x)) i ∙ F .pad-i x)

  -- CONTRAPOSITIVE, and the whole point of the split record: an
  -- INTERNAL refutation at one element of a fillable slot refutes every
  -- total point.  Nothing here is specific to inversion.
  no-point : (o : σ .ops) (i : σ .arities o) → Fills o i
           → (x : Fib .carrier (σ .sortOf o i))
           → (Domˢ o i ⊢ ¬G ⌈ x ⌉) → LaxPoint Fib → ⊥
  no-point o i F x k P = E.rec* (k x (point→dom P o i F x tt) Eq.refl)

  -- THEOREM.  A total point puts every composite in the image -- but
  -- only the composites: this is a map at `op o m⃗`, not at every m.
  point→img : (P : LaxPoint Fib) (o : σ .ops)
              (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
            → Imgˢ o (P .op o m⃗)
  point→img P o m⃗ = P .split o m⃗ , λ _ → tt

  -- ================================================================
  -- WHEN IS `⊗ˢ o ⊤` THE UNIT?  Exactly when o is surjective.
  -- ================================================================

  Covering : (P : LaxPoint Fib) (o : σ .ops) → Type (ℓ-max ℓ' ℓX)
  Covering P o = (m : Fib .carrier (σ .resultSort o))
               → Σ[ m⃗ ∈ ((a : σ .arities o) → Fib .carrier (σ .sortOf o a)) ]
                 (P .op o m⃗ Eq.≡ m)

  covering→img : (P : LaxPoint Fib) (o : σ .ops) → Covering P o → ⊤G ⊢ Imgˢ o
  covering→img P o cov m _ =
    splitEq o (cov m .snd) (P .split o (cov m .fst)) , λ _ → tt

  -- the converse needs `Honest`, and needs it for the same reason
  -- `Bridge` does: a splitting must recompose to the thing it splits.
  img→covering : (P : LaxPoint Fib) → Honest P → (o : σ .ops)
               → (⊤G ⊢ Imgˢ o) → Covering P o
  img→covering P hon o f m =
    Fib .parts o m (f m tt .fst) , hon o m (f m tt .fst)
