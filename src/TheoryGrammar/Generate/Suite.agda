{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A TEST SUITE WHOSE INPUTS COME FROM THE FUZZER.

  `SemanticAction.Suite` is

      passes (f at (w₁ ↦ v₁ ∷ w₂ ↦ v₂ ∷ []))

  -- the term under test written once, the cases in a table.  Both
  columns are written by hand there, and here neither is:

      _ : fuzzed P gd 8 16 2024 world (onWorld accepts) gives ?
      _ = refl

  The LEFT column is whatever the fuzzer drew and the RIGHT column is
  what the program said about it, so the whole table is DETERMINED.

  ==================================================================
  WHY `_gives_` IS `_≡_` AND WHY THE HOLE GOES ON THE RIGHT.

  `observed gives expected = observed ≡ expected`, and nothing else --
  the point is what that buys interactively.  Write the right side as `?`
  and the proof as `refl`:

      _ : suite₁ gives ?
      _ = refl

  and `refl` unifies the metavariable with the left side, so `C-c C-s`
  with normalisation (Solve constraints) prints the whole table back.
  NOT `C-c C-a`: there is nothing to search for, because the equation has
  already DETERMINED the hole -- which is the sharper version of the
  claim, and the reason this works at all.  Measured on `GenerateTests`'s
  `suite₁`/`suite₂`, both solve.

  So the suite is read OUT of the fuzzer rather than guessed and then
  checked, and once pasted in it is an ordinary `refl` regression test
  fixing both the draws and the program's answers.

  That only works because everything computes: the LCG is over
  `Agda.Builtin.Nat` primitives, the draws are `sup`-trees over
  `Eq.refl`s, and `Generate`'s `StrictPoint` exists precisely so that no
  `subst` appears under `Sh` to make the normal form stick.  A generator
  built on `LaxPoint`'s path would leave the hole unsolvable, which is
  the practical statement of the `subst` trap.

  ==================================================================
  REPRESENTATIONS.

  A draw is a world together with a term at it, and neither is usually
  what one wants to read.  A `Rep` is any function out of a draw, with
  three ways to build one:

      world       the index -- the generated input itself
      onWorld f   a program under test, run at the index
      viaA a      a SEMANTIC ACTION on the generated TERM

  `viaA` is the one the calculus supplies: `Action (μAt x) V` is
  `μAt x ⊢ Δ V`, an internal term, and applying it is `run` -- the single
  exit, in the `refl` line of a test, exactly where EXTERNALISE LATE
  puts it.

  §2 then gives ONE generic action, `sizeOf`, the number of constructor
  nodes.  It is derived from `GenDesc` ALONE: listing a layer's recursive
  positions needs exactly the two listings the generator already has
  (`enumAr` at a `⊗e`, the `Listed Y` of a `&e` clause).  So every
  description that can be generated can also be measured, with no
  further obligation on the theory or the grammar.

  PRIMITIVE: none.
-}
module TheoryGrammar.Generate.Suite where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed
open import TheoryGrammar.SemanticAction using (module Act)
open import TheoryGrammar.Generate

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓV ℓW ℓY : Level

-- 0.  THE ASSERTION.  Theory-free: once the table has been produced,
-- checking it is one equation.

infix 2 _gives_
_gives_ : {W : Type ℓW} {V : Type ℓY} → List (W × V) → List (W × V) → Type (ℓ-max ℓW ℓY)
observed gives expected = observed ≡ expected

sumL : List ℕ → ℕ
sumL []       = 0
sumL (n ∷ ns) = n + sumL ns

-- 1.  THE SUITE.  Parameters are `GenInd`'s, unchanged.

module FuzzSuite {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                 (Fib : Fibered σ ℓX ℓP) (ℓA : Level)
                 (X : Type ℓV) (xs : X → S)
                 (seekSplit : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
                            → Unit → List (Fib .Split o m))
                 (enumAr : (o : σ .ops) → Listed (σ .arities o))
                 where

  open GenInd Fib ℓA X xs seekSplit enumAr public
  -- `Act` needs only a carrier, and it is the SAME `CarrierNotation`
  -- application as `GenNotation`'s, so nothing here is ambiguous.
  open Act {σ = σ} (Fib .carrier) using (Δ; Action; run) public

  module _ (F : (x : X) → Functor (xs x)) where

    -- the generated grammar, as a type of the calculus
    μAt : (x : X) → TheoryTy ℓμ (xs x)
    μAt x m = μ F (x , m)

    -- 1a.  REPRESENTATIONS OF A DRAW.

    Rep : (x : X) (W : Type ℓW) → Type (ℓ-max ℓX (ℓ-max ℓμ ℓW))
    Rep x W = Draw F x → W

    -- the index: the generated input itself
    world : (x : X) → Rep x (Fib .carrier (xs x))
    world x d = d .fst

    -- a program under test, run at the index
    onWorld : (x : X) {V : Type ℓW}
            → (Fib .carrier (xs x) → V) → Rep x V
    onWorld x f d = f (d .fst)

    -- A SEMANTIC ACTION on the generated TERM.
    viaA : (x : X) {V : Type ℓW} → Action (μAt x) V → Rep x V
    viaA x a d = a (d .fst) (d .snd) .fst

    -- 1b. ONE GENERIC ACTION: the node count.

    posList : {s : S} (G : Functor s) → GenDesc G
            → (m : Fib .carrier s) (sh : Sh G m) → List (Pos G m sh)
    posList (⌜ B ⌝)  _          m sh       = []
    posList (Var x)  _          m sh       = tt* ∷ []
    posList (⊕e Y G) (gY , dG)  m (y , sh) = posList (G y) (dG y) m sh
    posList (&e Y G) (lY , dG)  m sh =
      bindL (lY .elts) λ y →
        map (λ p → y , p) (posList (G y) (dG y) m (sh y))
    posList (⊗e o G) dG m (sp , sh) =
      bindL (enumAr o .elts) λ a →
        map (λ p → a , p) (posList (G a) (dG a) _ (sh a))

    sizeOf : ((x : X) → GenDesc (F x)) → (x : X) → Rep x ℕ
    sizeOf gd x d =
      fold (λ _ → ℕ)
           (λ z m sh rec → suc (sumL (map rec (posList (F z) (gd z) m sh))))
           (x , d .fst) (d .snd)

    -- 1c.  THE TABLE.

    -- the fuzzer's inputs, failures dropped.  A draw that exhausts the
    -- size is not a test case and is not silently counted as one --
    -- `length (upStream …)` against `length (draws …)` is the report.
    draws : StrictPoint Fib → ((z : X) → UpDesc (F z))
          → (size count : ℕ) → (x : X) → Seed → List (Draw F x)
    draws P gd size count x sd = catMaybes (upStream F P gd size count x sd)

    table : (x : X) {W : Type ℓW} {V : Type ℓY}
          → Rep x W → Rep x V → List (Draw F x) → List (W × V)
    table x inR outR = map λ d → inR d , outR d

    -- ... AND ALL OF IT AT ONCE.  Fuzzer parameters and two
    -- representations in, a table out.  This is the thing that goes to
    -- the left of `gives`.
    fuzzed : StrictPoint Fib → ((z : X) → UpDesc (F z))
           → (size count : ℕ) → Seed → (x : X)
           → {W : Type ℓW} {V : Type ℓY} → Rep x W → Rep x V → List (W × V)
    fuzzed P gd size count sd x inR outR =
      table x inR outR (draws P gd size count x sd)
