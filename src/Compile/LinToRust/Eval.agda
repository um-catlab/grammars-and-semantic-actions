{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE VALUE SEMANTICS OF THE PURE FRAGMENT.

  Two presentations, and a bridge -- the same architecture
  `Compile.LinToISA.Machine` uses for its ISA, transplanted from a
  state monoid to a call-by-value λ:

    * `_⇓_`      a big-step evaluation RELATION.  Total as a
                 definition (it is an inductive family), and it is what
                 the correctness statement downstream is phrased in.
    * `evalRust` an EXECUTABLE evaluator, so that the tests are `refl`.

  and the bridge is that `evalRust` returns its own derivation:

      evalRust : (k : ℕ) (e : RExpr) → Maybe (Σ[ v ∈ RExpr ] (e ⇓ v))

  This is `exec-sound` made intrinsic.  In `LinToISA` the executable
  machine and the relational semantics were separate and a three-clause
  lemma identified them; here the evaluator simply carries the proof,
  which is strictly better and costs nothing, because unlike a machine
  step an evaluation step is not a total function.

  ------------------------------------------------------------------
  WHY THERE IS FUEL, AND WHY IT IS NOT A COMPROMISE
  ------------------------------------------------------------------

  `RExpr` is an UNTYPED λ-calculus with an enum, so it contains
  divergent terms (`(move |x0| (x0)(x0))(move |x0| (x0)(x0))`); no
  total `RExpr → RValue` exists, and pretending otherwise would be
  dishonest.  The evaluator therefore takes a step budget `k` and
  returns `nothing` when it runs out or gets stuck.

  Nothing in the SPECIFICATION mentions fuel.  The correctness
  statement is the simulation square

      t ⇓ₛ v   ⟹   compile t ⇓ compile v

  between the two RELATIONS, and `evalRust` is only how one observes
  it.  The image of the compiler is strongly normalising -- the source
  is linear, so β strictly decreases term size -- so on compiled input
  a large enough budget always suffices; the `refl` tests below exhibit
  concrete budgets.  Establishing "large enough" uniformly is the
  source normaliser's job, which is `Compile/Semantics/`'s, and this
  file deliberately does not duplicate it.

  ------------------------------------------------------------------
  CALL BY VALUE, AND MOVE SEMANTICS
  ------------------------------------------------------------------

  `⇓call` evaluates the function, then the argument, then the body --
  Rust's order, and Rust's strictness.  The argument is a VALUE when it
  is substituted, which is what "the closure takes ownership of its
  argument" means operationally.

  ------------------------------------------------------------------
  SUBSTITUTION IS NAIVE, AND THAT IS CORRECT HERE
  ------------------------------------------------------------------

  `substE` does not rename, so in general it would capture.  It does
  not capture on anything this development produces, for two
  independent reasons, both worth stating because they are exactly the
  two disciplines the backend is about:

    (1) SCOPING.  `Codegen` names binders by LEVEL, so along any path
        from the root no two binders share a name and no source
        variable is ever shadowed.
    (2) LINEARITY.  Call-by-value substitutes VALUES, and a value
        reached from a closed term is closed, so there are no free
        names to capture in the first place.

  `substE` does stop at a rebinding of the same name (`ifE (eqIdent x
  (bnd n))`), so it is at least the standard capture-AVOIDING-by-
  stopping definition rather than a wrong one.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout, and marked: `substE`, `_⇓_`, `evalRust` and its
  three helpers, `⇓-isVal`.  This is a language being given a
  semantics, not a program in the calculus.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Eval where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.LinToRust.Syntax public

-- ==================================================================
-- SUBSTITUTION.
-- ==================================================================

-- PRIMITIVE (phase 1): the named eliminator for `Bool` at `RExpr`.
-- Never an extended lambda: Agda identifies those nominally.
ifE : Bool → RExpr → RExpr → RExpr
ifE true  x y = x
ifE false x y = y

-- PRIMITIVE (phase 1)
substE : Ident → RExpr → RExpr → RExpr
substE x v (rVar y)       = ifE (eqIdent x y) v (rVar y)
substE x v (rClos n b)    =
  ifE (eqIdent x (bnd n)) (rClos n b) (rClos n (substE x v b))
substE x v (rCall f a)    = rCall (substE x v f) (substE x v a)
substE x v (rCtor c)      = rCtor c
substE x v (rMatch s a b) = rMatch (substE x v s) (substE x v a) (substE x v b)
substE x v (rLet n e b)   =
  rLet n (substE x v e) (ifE (eqIdent x (bnd n)) b (substE x v b))

-- ==================================================================
-- THE VALUE SEMANTICS.  Call by value, Rust's order.
-- ==================================================================

infix 4 _⇓_

data _⇓_ : RExpr → RExpr → Type₀ where       -- PRIMITIVE (phase 1)

  ⇓clos : (n : ℕ) (b : RExpr) → rClos n b ⇓ rClos n b
  ⇓ctor : (c : Ctor)          → rCtor c    ⇓ rCtor c

  -- `(f)(a)`: evaluate the callee, evaluate the argument, MOVE it in
  ⇓call : {f a b w : RExpr} {n : ℕ} {va : RExpr}
        → f ⇓ rClos n b → a ⇓ va → substE (bnd n) va b ⇓ w
        → rCall f a ⇓ w

  -- `{ let xn = e; b }`: an immutable binding is a β-redex
  ⇓let  : {e b w ve : RExpr} {n : ℕ}
        → e ⇓ ve → substE (bnd n) ve b ⇓ w
        → rLet n e b ⇓ w

  -- `match (s) { U::A => a, U::B => b }`
  ⇓matchA : {s a b w : RExpr} → s ⇓ rCtor cA → a ⇓ w → rMatch s a b ⇓ w
  ⇓matchB : {s a b w : RExpr} → s ⇓ rCtor cB → b ⇓ w → rMatch s a b ⇓ w

-- an evaluated expression really is a value.  PRIMITIVE (phase 1).
⇓-isVal : {e v : RExpr} → e ⇓ v → IsVal v
⇓-isVal (⇓clos n b)    = valClos n b
⇓-isVal (⇓ctor c)      = valCtor c
⇓-isVal (⇓call _ _ d)  = ⇓-isVal d
⇓-isVal (⇓let _ d)     = ⇓-isVal d
⇓-isVal (⇓matchA _ d)  = ⇓-isVal d
⇓-isVal (⇓matchB _ d)  = ⇓-isVal d

-- ==================================================================
-- ... AND THE SEMANTICS IS DETERMINISTIC.
--
-- Stated in the `Eq`-world, deliberately: the `⇓call` clause has to
-- identify two derivations whose subject expressions are only
-- PROPOSITIONALLY equal, and matching `Eq.refl` makes that
-- identification definitional.  With a cubical `Path` the same proof
-- needs `subst` on the derivation, which is neither structurally
-- smaller (the termination checker refuses it) nor reducing (the
-- known trap).
-- ==================================================================

-- PRIMITIVE (phase 1)
⇓-det : {e v w : RExpr} → e ⇓ v → e ⇓ w → v Eq.≡ w
⇓-det (⇓clos n b) (⇓clos .n .b) = Eq.refl
⇓-det (⇓ctor c)   (⇓ctor .c)    = Eq.refl
⇓-det (⇓call df da d) (⇓call df' da' d')
  with ⇓-det df df' | ⇓-det da da'
... | Eq.refl | Eq.refl = ⇓-det d d'
⇓-det (⇓let de d) (⇓let de' d') with ⇓-det de de'
... | Eq.refl = ⇓-det d d'
⇓-det (⇓matchA ds d) (⇓matchA ds' d') = ⇓-det d d'
⇓-det (⇓matchB ds d) (⇓matchB ds' d') = ⇓-det d d'
⇓-det (⇓matchA ds d) (⇓matchB ds' d') with ⇓-det ds ds'
... | ()
⇓-det (⇓matchB ds d) (⇓matchA ds' d') with ⇓-det ds ds'
... | ()

-- ==================================================================
-- THE EXECUTABLE EVALUATOR, WHICH CARRIES ITS OWN SOUNDNESS PROOF.
--
-- `Result e` is "either nothing, or a value together with a derivation
-- that `e` evaluates to it".  So there is no `eval-sound` lemma to
-- state: the type IS the lemma, and every `refl` test below is
-- therefore a test of the RELATION, not of a separate function that
-- happens to agree with it.
-- ==================================================================

Result : RExpr → Type₀
Result e = Maybe (Σ[ v ∈ RExpr ] (e ⇓ v))

-- PRIMITIVE (phase 1): postcomposition of a derivation.  This is the
-- only way a `Result` is ever built from another one.
bindD : {e e' : RExpr} → ((w : RExpr) → e' ⇓ w → e ⇓ w) → Result e' → Result e
bindD f nothing        = nothing
bindD f (just (w , d)) = just (w , f w d)

mutual

  -- PRIMITIVE (phase 1): the evaluator.  `k` is the step budget.
  evalRust : (k : ℕ) (e : RExpr) → Result e
  evalRust zero    e             = nothing
  evalRust (suc k) (rVar x)      = nothing         -- stuck: free variable
  evalRust (suc k) (rClos n b)   = just (rClos n b , ⇓clos n b)
  evalRust (suc k) (rCtor c)     = just (rCtor c   , ⇓ctor c)
  evalRust (suc k) (rCall f a)   = evCall k (evalRust k f) (evalRust k a)
  evalRust (suc k) (rLet n e b)  = evLet k n b (evalRust k e)
  evalRust (suc k) (rMatch s a b) = evMatch k a b (evalRust k s)

  -- PRIMITIVE (phase 1)
  evCall : (k : ℕ) {f a : RExpr} → Result f → Result a → Result (rCall f a)
  evCall k nothing            _                  = nothing
  evCall k (just _)           nothing            = nothing
  evCall k (just (vf , df))   (just (va , da))   = evApp k vf va df da

  -- PRIMITIVE (phase 1): the one place a callee's SHAPE is inspected.
  -- Everything but a closure is stuck, which is the operational
  -- reading of "you can only call a `Fn`".
  evApp : (k : ℕ) {f a : RExpr} (vf va : RExpr) → f ⇓ vf → a ⇓ va
        → Result (rCall f a)
  evApp k (rClos n b) va df da =
    bindD (λ w d → ⇓call df da d) (evalRust k (substE (bnd n) va b))
  evApp k (rVar _)       va df da = nothing
  evApp k (rCall _ _)    va df da = nothing
  evApp k (rCtor _)      va df da = nothing
  evApp k (rMatch _ _ _) va df da = nothing
  evApp k (rLet _ _ _)   va df da = nothing

  -- PRIMITIVE (phase 1)
  evLet : (k : ℕ) (n : ℕ) (b : RExpr) {e : RExpr} → Result e → Result (rLet n e b)
  evLet k n b nothing         = nothing
  evLet k n b (just (ve , de)) =
    bindD (λ w d → ⇓let de d) (evalRust k (substE (bnd n) ve b))

  -- PRIMITIVE (phase 1)
  evMatch : (k : ℕ) (a b : RExpr) {s : RExpr} → Result s → Result (rMatch s a b)
  evMatch k a b nothing          = nothing
  evMatch k a b (just (vs , ds)) = evArm k a b vs ds

  -- PRIMITIVE (phase 1): the scrutinee's constructor picks the arm.
  evArm : (k : ℕ) (a b : RExpr) {s : RExpr} (vs : RExpr) → s ⇓ vs
        → Result (rMatch s a b)
  evArm k a b (rCtor cA)     ds = bindD (λ w d → ⇓matchA ds d) (evalRust k a)
  evArm k a b (rCtor cB)     ds = bindD (λ w d → ⇓matchB ds d) (evalRust k b)
  evArm k a b (rVar _)       ds = nothing
  evArm k a b (rClos _ _)    ds = nothing
  evArm k a b (rCall _ _)    ds = nothing
  evArm k a b (rMatch _ _ _) ds = nothing
  evArm k a b (rLet _ _ _)   ds = nothing

-- ==================================================================
-- THE EXIT.  `valOf` forgets the derivation; it is used only in the
-- `refl` lines, here and in `Codegen`.
-- ==================================================================

valOf : {e : RExpr} → Result e → Maybe RExpr
valOf nothing        = nothing
valOf (just (v , _)) = just v

-- ==================================================================
-- OBSERVATION.  The semantics computes.
-- ==================================================================

-- a value evaluates to itself
_ : valOf (evalRust 1 (rCtor cA)) ≡ just (rCtor cA)
_ = refl

_ : valOf (evalRust 1 (rClos 0 (rVar (bnd 0)))) ≡ just (rClos 0 (rVar (bnd 0)))
_ = refl

-- β: the identity closure applied to an enum value
_ : valOf (evalRust 5 (rCall (rClos 0 (rVar (bnd 0))) (rCtor cA)))
  ≡ just (rCtor cA)
_ = refl

-- the identity applied to ITSELF is the identity
_ : valOf (evalRust 5 (rCall (rClos 0 (rVar (bnd 0))) (rClos 0 (rVar (bnd 0)))))
  ≡ just (rClos 0 (rVar (bnd 0)))
_ = refl

-- `match`, both arms
_ : valOf (evalRust 5 (rMatch (rCtor cA) (rCtor cB) (rCtor cA))) ≡ just (rCtor cB)
_ = refl

_ : valOf (evalRust 5 (rMatch (rCtor cB) (rCtor cB) (rCtor cA))) ≡ just (rCtor cA)
_ = refl

-- an immutable `let` is a β-redex
_ : valOf (evalRust 5 (rLet 3 (rCtor cB) (rVar (bnd 3)))) ≡ just (rCtor cB)
_ = refl

-- a free variable is STUCK, not a value -- this is what makes the
-- scoping discipline of `Codegen` load-bearing
_ : valOf (evalRust 5 (rVar (fre 0))) ≡ nothing
_ = refl

-- and the budget really is a budget
_ : valOf (evalRust 1 (rCall (rClos 0 (rVar (bnd 0))) (rCtor cA))) ≡ nothing
_ = refl
