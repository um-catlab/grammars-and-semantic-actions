{-
  THE FIELD INSTANCE: A THEORY WITH NO TOTAL POINT.

  `Fibered` holds only `carrier`/`Split`/`parts`; `op`/`split`/
  `parts-split` were factored into `LaxPoint` so that PARTIAL algebras
  keep the calculus.  This instance is the witness that the distinction
  has content: a signature whose `Fibered` exists and whose `LaxPoint`
  is refutable, with the obstruction LOCATED at the one partial
  operation -- the four-operation ring fragment is the same promodel,
  restricted along `ιR`, and it has a total honest point.

    Base      𝔽₃ and the five-operation signature, `Split invOp m = Nz m`
              -- EMPTY at zero -- plus the ring fragment
    Partial   the internal theorems at 𝔽₃, `⊗ˢ invOp ⊤ ⊣⊢ ¬G ⌈ f0 ⌉` in
              BOTH directions, and the decision `⊤ ⊢ Dec⟨ ⊗ˢ invOp ⊤ ⟩`
    NoPoint   `LaxPoint fldFib → ⊥`, and `LaxPoint rngFib` inhabited
    Joint     the same refutation through `TheoryGrammar.Domain`, the
              lemma `Heap/Joint` also uses
    Tests     `refl` at 𝔽₃

  There used to be a `Field/Domain` here holding the slotwise
  `Imgˢ`/`Domˢ`/`no-point`.  It was generic in the `Fibered` and was read
  from outside the field, so it is now `TheoryGrammar.Domain`'s
  `DomainOf`, alongside the joint form that supersedes it.

  THE CAVEAT, proved rather than remarked (`NoPoint.no-img-zero`):
  `⊗ˢ o ⊤` is the image of o, not its domain.  `zeroOp` is total and its
  image is a proper subgrammar, so `⊗ˢ o ⊤ = ⊤` is `Covering`
  (surjectivity), and the domain of definition lives one sort over.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field where

open import TheoryGrammar.Instances.Field.Base    public
open import TheoryGrammar.Instances.Field.Partial public
open import TheoryGrammar.Instances.Field.NoPoint public
open import TheoryGrammar.Instances.Field.Joint   public
open import TheoryGrammar.Instances.Field.Tests
