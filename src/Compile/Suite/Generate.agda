{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  GENERATING CLOSED LINEAR λ-TERMS, IN THE FIBRE.

  ------------------------------------------------------------------
  WHY THIS IS NOT AN INSTANCE OF `TheoryGrammar.Generate`
  ------------------------------------------------------------------

  `TheoryGrammar/Generate.agda` is the generic generator: give it a
  `Functor` description of an inductive grammar plus the theory's
  `seekSplit`/`enumAr`, and `genμ` enumerates in the fibre while `upμ`
  fuzzes bottom-up.  `LinLam`'s `Tm` is not reachable by it, for TWO
  independent reasons, and both are worth stating because each names a
  real limit rather than an omission.

  (1) `Functor`'s recursive former is

          Var : (x : X) → Functor (xs x)

      and `Inductive.nx` sends a `Var` position to `(x , m)` -- THE SAME
      WORLD.  `LinLam/Syntax`'s header says what abstraction is here:

          lamT : (λ u → Tm (true ∷ u)) ⊢ TmG

      -- reindexing along weakening, i.e. a recursive occurrence at a
      DIFFERENT world.  No `Functor` denotes that.  (`LinLam/DB.agda`'s
      `DBF` does have a description, and it pays for it by making the
      binder a separate SORT -- `⊗e lamOp` with a name slot -- which is a
      different calculus from the usage-indexed one the backends compile.)

  (2) `upμ` -- the bottom-up fuzzer -- needs a `StrictPoint linFib`, i.e.
      a TOTAL `opU appop : Usage → Usage → Usage` with
      `Use⊎ u₁ u₂ (opU u₁ u₂)`.  There is none, and `Context.agda` says
      why in one line: "joining two usages is PARTIAL, undefined exactly
      when they both claim a variable".  `Use⊎`'s missing `(true,true)`
      constructor IS linearity, so a total point would BE a proof that
      the calculus is not linear.  Bottom-up generation is unavailable at
      this theory as a matter of mathematics.

  So what is written below is `Generate`'s TOP-DOWN direction, by hand,
  for a family that has no description -- and it is stated in
  `Generate`'s own internal vocabulary:

      seekTm : ℕ → Seek TmG              Seek A = ⊤G ⊢ ⋁ A,  ⋁ A m = List (A m)

  `Seek` is the dual of `View.Probe P = ⊤G ⊢ Dec⟨ P ⟩` and lives in the
  ADDITIVE fragment (`Generate.GenNotation` takes a bare carrier), so a
  generator is an internal term here exactly as it is there.  Nothing
  about the search space is claimed when it is empty -- that is the
  `findΣ`/`decΣ` asymmetry `Enumerable.agda`'s header records, and it is
  why no completeness proof appears below.

  ------------------------------------------------------------------
  WHAT COMPLETENESS THERE IS, AND WHERE
  ------------------------------------------------------------------

  `Generate.agda`'s refinement of that asymmetry says Σ-positions need no
  completeness and Π-positions do.  Both show up here:

      enumSolo    Σ    the variable, if the usage licenses one
      enumSplit   Σ    `linFib .Split appop u`, ALL of it -- and it is
                       finite because `Use⊎` forces the three usages to
                       have equal length, so a split of `u` is a choice
                       of side per live slot: 2^(live u) of them.
      the two premises of `tapp`   -- the arity, filled at every slot

  `enumSplit` is written total anyway, because it costs nothing: a split
  is decided slot by slot, and every slot has one or two options.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all of it: a generator is a recursion on a carrier (the usage)
  and on the fuel, which is what building a search space is allowed to
  do.  `seekTm` is the internal statement of the result.
-}
open import Cubical.Foundations.Prelude

module Compile.Suite.Generate where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; map; _++_; length)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Generate using (bindL; module GenNotation)

open import TheoryGrammar.Instances.LinLam.Syntax

-- `⋁` and `Seek`, at this carrier.  The SAME `CarrierNotation`
-- application `Context.agda` already made, so nothing is ambiguous.
open GenNotation (linFib .carrier) using (⋁; Seek)

-- ==================================================================
-- §1  THE LEAVES.
--
-- `Empty` and `Solo` are recursive predicates on the usage, so their
-- search spaces are the same recursion with a `List` around it.  Both
-- are complete, and both have at most one element -- `Solo` says
-- "exactly one variable is live", so a usage licenses one variable
-- reference or none.
-- ==================================================================

enumEmpty : (u : Usage) → List (Empty u)
enumEmpty []          = tt ∷ []
enumEmpty (true  ∷ u) = []
enumEmpty (false ∷ u) = enumEmpty u

enumSolo : (u : Usage) → List (Solo u)
enumSolo []          = []
enumSolo (true  ∷ u) = enumEmpty u
enumSolo (false ∷ u) = enumSolo u

-- ==================================================================
-- §2  THE SPLITTINGS.  This is `linFib .Split appop`, enumerated -- the
-- theory's obligation, which for strings is `enumSplitL` and here has
-- to be written because the linear theory has no listing module.
--
-- One clause per constructor of `Use⊎`: a live slot goes LEFT or RIGHT
-- (two ways), a dead slot goes nowhere (one way), and the empty usage
-- splits exactly one way.  The absent `(true,true)` case is linearity,
-- and it is absent here for the same reason it is absent there.
-- ==================================================================

Split⊎ : Usage → Type₀
Split⊎ u = Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ] Use⊎ u₁ u₂ u

enumSplit : (u : Usage) → List (Split⊎ u)
enumSplit []          = ([] , [] , unil) ∷ []
enumSplit (true  ∷ u) =
     map (λ z → (true  ∷ z .fst) , (false ∷ z .snd .fst) , uleft  (z .snd .snd))
         (enumSplit u)
  ++ map (λ z → (false ∷ z .fst) , (true  ∷ z .snd .fst) , uright (z .snd .snd))
         (enumSplit u)
enumSplit (false ∷ u) =
     map (λ z → (false ∷ z .fst) , (false ∷ z .snd .fst) , uskip (z .snd .snd))
         (enumSplit u)

-- ==================================================================
-- §3  THE TERMS.
--
-- `n` is the DEPTH bound, exactly as `genμ`'s fuel is: it bounds the
-- height of the derivation, not the size of the world.  Every term
-- produced is well-resourced at `u` BY CONSTRUCTION -- `tapp` is given a
-- splitting of `u` and its premises are generated at the parts -- so
-- there is no filter and no rejection step, which is the whole reason
-- generation happens in the fibre.
-- ==================================================================

enumTm : ℕ → (u : Usage) → List (Tm u)
enumTm zero    u = []
enumTm (suc n) u =
     map tvar (enumSolo u)
  ++ ( map tlam (enumTm n (true ∷ u))
     ++ bindL (enumSplit u) (λ z →
          bindL (enumTm n (z .fst)) (λ f →
            map (λ a → tapp (z .snd .snd) f a) (enumTm n (z .snd .fst)))) )

-- THE INTERNAL STATEMENT.  `Seek TmG = ⊤G ⊢ ⋁ TmG`: at every world, the
-- terms of that world that this bound reaches.  Dual to `View.Probe`.
seekTm : ℕ → Seek TmG
seekTm n u _ = enumTm n u

-- ... and the exit the suite consumes: closed terms are the fibre over
-- the unit of the usage monoid.
closedTms : ℕ → List (Tm [])
closedTms n = enumTm n []

-- ==================================================================
-- §4  IT COMPUTES, AND IT PRODUCES THE TERMS THE BACKENDS ARE TESTED ON.
--
-- Depth 3 is `λx.x` and `(λx.x)(λx.x)` -- `Showcase`'s two witnesses,
-- generated rather than written.  That they are the ONLY two is the
-- content: at depth 3 a closed linear term is either an abstraction over
-- a variable or an application of two such.
-- ==================================================================

_ : length (closedTms 0) ≡ 0
_ = refl

_ : length (closedTms 1) ≡ 0
_ = refl

_ : length (closedTms 2) ≡ 1
_ = refl

_ : closedTms 2 ≡ idLin ∷ []
_ = refl

_ : closedTms 3 ≡ idLin ∷ selfApp ∷ []
_ = refl

-- the OPEN fibres are generated too, which is what makes the recursion
-- go under `tlam` at all: `Solo (true ∷ [])` is inhabited, so `x` is a
-- term at the one-variable usage ...
_ : enumTm 1 (true ∷ []) ≡ tvar tt ∷ []
_ = refl

-- ... and at the TWO-variable usage there is no variable at all, because
-- `Solo` says exactly one is live.  What there is instead is `x y` and
-- `y x`: the splitting is CHOSEN, not checked, and the two choices are
-- the two terms.  (These are `Simulation.noBlindBackend`'s witnesses --
-- distinct β-normal terms at one usage -- generated rather than written.)
_ : enumTm 2 (true ∷ true ∷ [])
  ≡ tapp (uleft (uright unil)) (tvar tt) (tvar tt)
  ∷ tapp (uright (uleft unil)) (tvar tt) (tvar tt)
  ∷ []
_ = refl
