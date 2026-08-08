{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE LINEAR λ-CALCULUS WITH NUMBERS.

  ------------------------------------------------------------------
  WHY BASE VALUES ARE REQUIRED AND NOT A CONVENIENCE
  ------------------------------------------------------------------

  `TheoryGrammar/Instances/LinLam/Syntax.agda`'s `Tm` is var/app/lam
  and nothing else, so EVERY closed value of it is a λ.  The three
  backends therefore all answer "a closure", and
  `Compile/ClosureConv/Correct.agda`'s `valuesCollapse` is the exact
  statement of the damage: the observation is CONSTANT on values.

  The usual escape -- Church numerals -- is not available, and the
  reason is structural rather than awkward.  `two = λf. λx. f (f x)`
  uses `f` twice, and `Use⊎` has no

      utwo : Use⊎ (true ∷ u₁) (true ∷ u₂) (true ∷ u)

  constructor.  Duplication is not merely discouraged here; it is
  UNTYPEABLE.  So a linear calculus that is to compute a number must be
  given one.

  ------------------------------------------------------------------
  THE SHAPE, AND WHY IT IS THAT SHAPE
  ------------------------------------------------------------------

  It is `Compile/ArithToARM/Base.agda`'s `Exp`, verbatim:

      elit : Empty u → ℕ → Exp u          a literal consumes NOTHING
      eadd : Use⊎ u₁ u₂ u → …             a primitive SPLITS the usage

  A literal is a closed leaf, so its usage must be empty -- otherwise a
  variable would be silently dropped.  A binary primitive is exactly
  `napp`'s shape with a different head: the `Use⊎` is what says the two
  operands consume disjoint halves of the context, and it is the same
  premise `⊗ˢ` supplies for application.  So `nadd` needs no new
  linearity argument; it reuses application's.

  ------------------------------------------------------------------
  A NEW TYPE, NOT AN EXTENSION OF `Tm`
  ------------------------------------------------------------------

  Adding two constructors to `L.Tm` would put a hole in every function
  that matches on it -- `Convert.convert`, `LinToRust.compileE`,
  `Correct.agda`'s inductions, `Compare.agda`'s harness -- so the whole
  of the existing chain would go from green to holed at once.  `NTm` is
  a separate type with `fromTm : L.Tm u → NTm u` embedding the old one,
  which keeps every existing `refl` exactly as it was and lets the new
  backends be checked AGAINST the old ones on the shared fragment:
  `Compile/LinNum/ARM.agda` §8 pins `asmN (fromTm idLin) ≡ Emit.asmId`,
  i.e. the two emitters agree character for character where both apply.

  PHASE.  Phase 1: this is the definition of a syntax.
-}
open import Cubical.Foundations.Prelude

module Compile.LinNum.Syntax where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.Data.Equality as Eq

-- the usage promodel and the OLD terms, re-exported so that the
-- backends downstream need not name two modules for one language
open import TheoryGrammar.Instances.LinLam.Syntax as L
  using (Usage; Use⊎; unil; uleft; uright; uskip; Empty; Solo; Tm; tvar; tapp; tlam)
  public

-- ==================================================================
-- §1  THE TERMS.  Five constructors; the first three are `L.Tm`'s.
-- ==================================================================

data NTm : Usage → Type₀ where
  nvar : ∀ {u} → Solo u → NTm u
  napp : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → NTm u₁ → NTm u₂ → NTm u
  nlam : ∀ {u} → NTm (true ∷ u) → NTm u
  nlit : ∀ {u} → Empty u → ℕ → NTm u                              -- NEW
  nadd : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → NTm u₁ → NTm u₂ → NTm u     -- NEW

-- ==================================================================
-- §2  THE OLD LANGUAGE, EMBEDDED.  Index-preserving, so a term that
-- was linear stays linear -- there is nothing to check.
-- ==================================================================

fromTm : ∀ {u} → Tm u → NTm u
fromTm (tvar s)      = nvar s
fromTm (tapp sp f a) = napp sp (fromTm f) (fromTm a)
fromTm (tlam b)      = nlam (fromTm b)

-- ==================================================================
-- §3  THE TERMS THAT COMPUTE.
--
-- Every usage side condition below is `tt`, because `Empty` and `Solo`
-- are RECURSIVE PREDICATES rather than data -- the same reason
-- `Compile/Suite/Terms.agda`'s `emptyW` returns at most one witness.
-- ==================================================================

-- a literal, alone: `41`
lit41 : NTm []
lit41 = nlit tt 41

-- `40 + 2`, with the empty context split as `[] ⊎ []`
sum42 : NTm []
sum42 = nadd unil (nlit tt 40) (nlit tt 2)

-- `λx. x + 1`.  The body is at usage `true ∷ []`, split as
-- `(true ∷ []) ⊎ (false ∷ [])`: the variable goes LEFT, the literal
-- takes the empty half.  That split is the whole of the linearity
-- argument for `+`.
inc : NTm []
inc = nlam (nadd (uleft unil) (nvar tt) (nlit tt 1))

-- THE TARGET.  `(λx. x + 1) 41`
incApp : NTm []
incApp = napp unil inc lit41

-- `λx. λy. x + y`, and it applied to 40 and 2 -- two binders, so the
-- inner block CAPTURES the outer variable, and the answer is a number
-- that came out of a closure's environment
addFn : NTm []
addFn = nlam (nlam (nadd (uright (uleft unil)) (nvar tt) (nvar tt)))

addApp : NTm []
addApp = napp unil (napp unil addFn (nlit tt 40)) (nlit tt 2)

-- `(λf. f 41) (λx. x + 1)` -- a number produced by a call through a
-- variable, which is the case where the ARM backend's `blr` is exercised
applyInc : NTm []
applyInc = napp unil (nlam (napp (uleft unil) (nvar tt) (nlit tt 41))) inc

-- a bigger one, to check the allocator: `((λx.λy. x + y) 40 2) + 101`
sum143 : NTm []
sum143 = nadd unil addApp (nlit tt 101)

-- ==================================================================
-- §4  WHAT IS STILL UNWRITABLE.
--
-- `λx. x + x` would need `Use⊎ (true ∷ []) (true ∷ []) (true ∷ [])`,
-- and the four constructors of `Use⊎` are `unil`, `uleft`, `uright`,
-- `uskip` -- there is no clause producing `true` from `true`/`true`.
-- Stated here rather than proved because the type is empty by pattern
-- matching alone; `Compile/Suite/Terms.agda`'s `allSplits` enumerates
-- the whole of it and never offers one.
-- ==================================================================
