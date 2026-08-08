{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE INTERMEDIATE REPRESENTATION, AND WHY AN OPTIMISATION PASS COSTS
  NOTHING TO APPLY TO IT.

  `Check.linear?` decides `Lin`, and `Lin` is not merely a predicate:

      Lin m = Σ[ u ∈ Usage ] (length u ≡ m .fst)
                           × Σ[ e ∈ Tm u ] (eraseS e ≡ skel (m .snd))

  its witness CONTAINS a `Tm u` -- a term of `LinLam.Syntax`, where
  linearity is structural because `tapp` carries a `Use⊎` and `Use⊎` has
  no `(true,true)` clause.  So the checker does not return a certificate
  ABOUT the de Bruijn term; it returns the intrinsically-linear term
  itself.  That term is the IR, and this file is the seam where the
  pipeline picks it up.

  Nothing in the repository connected the two before: `Check` stopped at
  a `Bool` (`linearB`), `Opt` started from a `Tm u` written by hand, and
  `Chain.Pipeline` bridged them by pulling `linRes .fst` out with
  `witness` in a test.  `optimised` below is that bridge as a TERM.

  §1  WHAT HAS TO BE DROPPED, AND WHY IT IS EXACTLY ONE COMPONENT.

  A pass CHANGES the term, so it cannot preserve

      eraseS e ≡ skel (m .snd)          -- "e erases to THIS de Bruijn term"

  and no amount of care will make it.  That equation is what makes `Lin`
  a statement about a particular input, and an optimiser's output is by
  design not that input.  So the IR is `Lin` with that one component
  removed:

      LinIR m = Σ[ u ∈ Usage ] (length u ≡ m .fst) × Tm u

  read as "there is a linear term at this scope".  `forgetSkel` is the
  projection, and it is the ONLY thing given up -- the usage and the
  scope equation both survive, which §2 is about.

  §2  ... AND WHY THE REST SURVIVES FOR FREE.  This is the payoff.

  A pass is `Pass = TmG ⊢ TmG` over `linFib`, i.e.

      f : (u : Usage) → Tm u → Tm u

  -- the SAME `u` on both sides, because `_⊢_` preserves the index.  So
  `liftPass f` can apply `f` under the existential and hand back `len`
  UNTOUCHED:

      liftPass f m (u , len , e) = u , len , f u e
                                       ^^^
                                       not reconstructed, not transported

  Read what that one line discharges.  `len : length u ≡ m .fst` is the
  scope bookkeeping -- "this term has as many slots as the source scope
  had".  For a pass over a bare syntax `DB k → DB k` that is an
  obligation: you prove separately that the optimiser did not change the
  number of free variables.  Here there is nothing to prove, because the
  pass never had access to a different usage to return.  "An
  optimisation neither invents nor drops a free variable" is not a
  theorem about `optimise`; it is the type of `Pass`.

  And it is uniform in the pass: `betaPass`, `etaPass`, `dcePass` and
  their composite all lift by the same line, because the only thing
  `liftPass` uses is that a pass is index-preserving.

  §3  PHASE.  `forgetSkel`, `liftPass` and `irPack` are PRIMITIVES, and
  all three for one reason: they cross a theory boundary.  `LinIR` is a
  grammar over `dbFib` (indexed by `Term• = Σ[n] DBTm n`) whose content
  is a grammar over `linFib` (indexed by `Usage`) under a Σ, and
  `CarrierMap.Reindex` relates `Fibered` over ONE signature -- the two
  live over `λSig` and `monoidSig` respectively.  `Reindex.LinLam` is
  where that bridge is being built generically; until it lands, the Σ is
  written by hand and labelled.  Each of the three is one line and none
  of them decides anything.
-}
module TheoryGrammar.Instances.LinLam.IR where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Maybe using (Maybe)
open import Cubical.Data.List using (List; []; _∷_; length)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Instances.LinLam.DB
open import TheoryGrammar.Instances.LinLam.Check
open import TheoryGrammar.Instances.LinLam.Syntax
  using (Usage; Tm; Pass; idPass; _then_)
open import TheoryGrammar.Instances.LinLam.Opt
  using (betaPass; etaPass; dcePass; optimise)

-- §1  THE IR.  `Lin` with the erasure equation removed.

LinIR : TmG
LinIR m = Σ[ u ∈ Usage ] ((length u Eq.≡ m .fst) × Tm u)

-- PRIMITIVE (phase 1): the projection.  The erasure equation is the
-- one component an optimiser cannot preserve; everything else is
-- carried across untouched.
forgetSkel : Lin ⊢ LinIR
forgetSkel m (u , len , e , _) = u , len , e

-- §2  A PASS, LIFTED.  One line, and the line is the theorem.

-- PRIMITIVE (phase 1): a `linFib` term applied under the existential.
-- `len` is passed through rather than re-derived, and it can be
-- because `f` is index-preserving.
liftPass : Pass → (LinIR ⊢ LinIR)
liftPass f m (u , len , e) = u , len , f u e

-- ... and it is FUNCTORIAL, definitionally.
liftPass-id : liftPass idPass ≡ idg
liftPass-id = refl

liftPass-then : (f g : Pass) → liftPass (f then g) ≡ (liftPass g ∘g liftPass f)
liftPass-then f g = refl

-- §3 THE PIPELINE STAGE, AS A TERM. `Dec⟨ Lin ⟩` IS `Result (¬G Lin) Lin`,
-- so `mapR` applies the IR extraction on the success branch and leaves the
-- refutation alone.

checkLin : ⊤G ⊢ Result (¬G Lin) LinIR
checkLin = mapR (¬G Lin) LinIR forgetSkel ∘g linear?

-- THE WHOLE BACK END, parameterised by which pass to run: check linearity,
-- and on the success branch optimise the intrinsically linear term.
compileWith : Pass → ⊤G ⊢ Result (¬G Lin) LinIR
compileWith f = mapR (¬G Lin) LinIR (liftPass f) ∘g checkLin

compile : ⊤G ⊢ Result (¬G Lin) LinIR
compile = compileWith optimise

-- the individual passes, at the same type -- for tests that need to see
-- one rewrite at a time rather than the composite
compileβ compileη compileDCE : ⊤G ⊢ Result (¬G Lin) LinIR
compileβ   = compileWith betaPass
compileη   = compileWith etaPass
compileDCE = compileWith dcePass

-- §4 THE OBSERVATIONS. `irPack` bundles the existential so the IR can be
-- read out as a value; `runΔ` at it is the single exit, and it belongs in
-- a test.

LinTm : Type₀
LinTm = Σ[ u ∈ Usage ] Tm u

-- PRIMITIVE (phase 1): the same Σ as `LinIR`, with the scope equation
-- dropped because an observation does not need it.
irPack : LinIR ⊢ Δ LinTm
irPack m (u , _ , e) = (u , e) , tt

-- ... and the usage alone, which is what "how many free variables does
-- the output have" asks for
irUsage : LinIR ⊢ Δ Usage
irUsage m (u , _ , _) = u , tt

runIR : (⊤G ⊢ Result (¬G Lin) LinIR) → Term• → Maybe LinTm
runIR p = runΔ LinTm (¬G Lin) (mapR (¬G Lin) (Δ LinTm) irPack ∘g p)
