{-
  THE FIELD INSTANCE: A THEORY WITH NO TOTAL POINT.

  `Fibered` holds only `carrier`/`Split`/`parts`; `op`/`split`/
  `parts-split` were factored into `LaxPoint` so that PARTIAL algebras
  keep the calculus.  This instance is the witness that the distinction
  has content: a signature whose `Fibered` exists and whose `LaxPoint`
  is refutable.

    Base      𝔽₃, the five-operation signature, `Split invOp m = Nz m`
              -- EMPTY at zero -- and the four-operation ring fragment
              (same promodel, restricted along `ιR`) with its total,
              honest point
    Domain    generic: `Imgˢ o = ⊗ˢ o ⊤` (the IMAGE) and `Domˢ o i`
              (the DOMAIN at slot i); what a `LaxPoint` forces on each
    Partial   the internal theorems at 𝔽₃:
                  ⊗ˢ invOp ⊤ ⊣⊢ ¬G ⌈ f0 ⌉
                  Domˢ invOp _ ⊣⊢ ¬G ⌈ f0 ⌉
              and the decision `⊤ ⊢ Dec⟨ ⊗ˢ invOp ⊤ ⟩`
    NoPoint   `LaxPoint fldFib → ⊥`, and `LaxPoint rngFib` inhabited
    Tests     `refl` at 𝔽₃

  THE CAVEAT, proved rather than remarked (`NoPoint.no-img-zero`):
  `⊗ˢ o ⊤` is the image of o, not its domain.  `zeroOp` is total and its
  image is a proper subgrammar.  `⊗ˢ o ⊤ = ⊤` is exactly `Covering`
  (surjectivity of the point), and the domain of definition lives one
  sort over, as `Domˢ`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field where

open import TheoryGrammar.Instances.Field.Base    public
open import TheoryGrammar.Instances.Field.Domain  public
open import TheoryGrammar.Instances.Field.Partial public
open import TheoryGrammar.Instances.Field.NoPoint public
open import TheoryGrammar.Instances.Field.Tests
