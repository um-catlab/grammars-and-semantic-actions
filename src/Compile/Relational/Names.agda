{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE THREE INDEX MANIPULATIONS, TRANSPORTED ACROSS THE RELATION.

  `Opt.subS` -- the source's substitution -- is not a bare structural
  recursion.  Its three clauses call `coeTm` (transport along an
  equation of usages), `delT` (strengthening: drop a dead slot) and
  `insT` (weakening: insert a dead slot), because a linear substitution
  has to say WHERE the variable went and what happened to the slot it
  vacated.  The target's `substE` does none of this: it walks the
  expression and plants the argument.

  So before the substitution lemma can be stated, `Rel` has to be shown
  BLIND to all three:

      relCoe : Rel ν t e            → Rel ν (coeTm p t) e
      relDel : Rel ν y e            → Rel (del k ν) (delT m y) e
      relIns : Rel (del k ν) a e    → Rel ν (insT m a) e

  -- the TARGET expression is literally unchanged in all three.  That
  is the precise sense in which these are bookkeeping: they move a
  source term between usages without moving anything the compiler can
  see.

  ------------------------------------------------------------------
  WHY `del` IS THE RIGHT CONTRACTION
  ------------------------------------------------------------------

  `relDel`'s `rlam` case is where the definition of `del` earns itself.
  Going under a binder turns `m` into `mthere true m` and `ν` into
  `ext n ν`, so the induction hypothesis lands at

      del (suc k) (ext n ν)

  and the constructor wants `ext n (del k ν)`.  These are the SAME
  FUNCTION definitionally (`Base.del-ext`, which is `refl`), so the
  clause is the constructor applied to the hypothesis and nothing else.
  Had either been written pointfully there would be a `funExt` here and
  a `subst` at a family over a variable name assignment behind it.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1.  Everything here is a lemma about the primitives, stated in
  the `Eq`-world so that it reduces: `soloAt-shift` is used to rewrite
  INSIDE an application of a variable `ν`, which a cubical `Path` would
  leave as a stuck `transp`.
-}
open import Cubical.Foundations.Prelude

module Compile.Relational.Names where

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.LinToRust.Codegen
open import Compile.Relational.Base
import TheoryGrammar.Instances.LinLam.Syntax as L
import TheoryGrammar.Instances.LinLam.Opt as O

-- ==================================================================
-- §1  A SMART `rvar`.
--
-- `Rel`'s variable constructor pins the identifier to `ν (soloAt 0 u
-- s)` on the nose.  Every lemma below produces that identifier only up
-- to an `Eq`-equation, so this is the form they use.  Matching
-- `Eq.refl` makes the rewrite definitional, so nothing downstream gets
-- stuck.
-- ==================================================================

relVar : ∀ {u} {ν : NameF} (s : L.Solo u) {x : Ident}
       → ν (soloAt 0 u s) Eq.≡ x → Rel ν (L.tvar s) (rVar x)
relVar s Eq.refl = rvar s

-- ==================================================================
-- §2  `soloAt` AND THE OFFSET.
--
-- `soloAt` counts from an offset, and the offset only ever moves by
-- one, so a single shift law suffices.  PRIMITIVE (phase 1).
-- ==================================================================

soloAt-shift : (p : ℕ) (u : L.Usage) (s : L.Solo u)
             → soloAt (suc p) u s Eq.≡ suc (soloAt p u s)
soloAt-shift p []          ()
soloAt-shift p (true  ∷ u) s = Eq.refl
soloAt-shift p (false ∷ u) s = soloAt-shift (suc p) u s

-- ==================================================================
-- §3  THE POSITION LAWS FOR A DEAD SLOT.
--
-- Inserting or removing a `false` moves every position past it by one,
-- and `del` moves the assignment by one in the opposite direction, so
-- the composite is the identity on NAMES.  This is the only arithmetic
-- in the whole repair.
-- ==================================================================

del-soloAt← : ∀ {k u v} (m : O.Mark false k u v) (s : L.Solo v) (ν : NameF)
            → del k ν (soloAt 0 u (O.markF-Solo← m s)) Eq.≡ ν (soloAt 0 v s)
del-soloAt← (O.mhere {u}) s ν = Eq.sym (Eq.ap ν (soloAt-shift 0 u s))
del-soloAt← (O.mthere true  m) s ν = Eq.refl
del-soloAt← (O.mthere false m) s ν =
    Eq.ap (del _ ν) (soloAt-shift 0 _ (O.markF-Solo← m s))
  Eq.∙ del-soloAt← m s (tl ν)
  Eq.∙ Eq.sym (Eq.ap ν (soloAt-shift 0 _ s))

del-soloAt→ : ∀ {k u v} (m : O.Mark false k u v) (s : L.Solo u) (ν : NameF)
            → del k ν (soloAt 0 u s) Eq.≡ ν (soloAt 0 v (O.markF-Solo→ m s))
del-soloAt→ (O.mhere {u}) s ν = Eq.sym (Eq.ap ν (soloAt-shift 0 u s))
del-soloAt→ (O.mthere true  m) s ν = Eq.refl
del-soloAt→ (O.mthere false m) s ν =
    Eq.ap (del _ ν) (soloAt-shift 0 _ s)
  Eq.∙ del-soloAt→ m s (tl ν)
  Eq.∙ Eq.sym (Eq.ap ν (soloAt-shift 0 _ (O.markF-Solo→ m s)))


-- ==================================================================
-- §3.5  LIVENESS TRANSPORTS ALONG A DEAD SLOT.
--
-- `Mark b k u v` inserts a slot at `k`, which is exactly the
-- reindexing `dlift k`.  Liveness therefore moves both ways along it,
-- and that is what re-establishes `rlam`'s non-shadowing premise after
-- a strengthening or a weakening.  PRIMITIVE (phase 1).
-- ==================================================================

mark-live→ : ∀ {b k u v} (m : O.Mark b k u v) (p : ℕ)
           → LiveAt p u → LiveAt (dlift k p) v
mark-live→ O.mhere        p       l = l
mark-live→ (O.mthere true  m) zero l = tt
mark-live→ (O.mthere false m) zero ()
mark-live→ (O.mthere c m) (suc p) l = mark-live→ m p l

mark-live← : ∀ {k u v} (m : O.Mark false k u v) (p : ℕ)
           → LiveAt p v
           → Σ[ p₀ ∈ ℕ ] ((dlift k p₀ Eq.≡ p) × LiveAt p₀ u)
mark-live← O.mhere            zero    ()
mark-live← O.mhere            (suc p) l = p , Eq.refl , l
mark-live← (O.mthere true  m) zero    l = zero , Eq.refl , tt
mark-live← (O.mthere false m) zero    ()
mark-live← (O.mthere c m)     (suc p) l =
  let (p₀ , e , l₀) = mark-live← m p l
  in suc p₀ , Eq.ap suc e , l₀

-- ==================================================================
-- §4  THE RELATION IS BLIND TO ALL THREE.
-- ==================================================================

-- transport along an equation of usages: `coeTm` matches `Eq.refl`, so
-- this is not a `subst` and there is nothing to prove
relCoe : ∀ {u v} (p : u Eq.≡ v) {ν : NameF} {t : L.Tm u} {e : RExpr}
       → Rel ν t e → Rel ν (O.coeTm p t) e
relCoe Eq.refl r = r

-- STRENGTHENING
relDel : ∀ {k u v} (m : O.Mark false k u v) {ν : NameF}
         {y : L.Tm v} {e : RExpr}
       → Rel ν y e → Rel (del k ν) (O.delT m y) e
relDel m (rvar s)       = relVar (O.markF-Solo← m s) (del-soloAt← m s _)
relDel m (rapp {sp = s} rf ra) with O.delSplit m s
... | (_ , _ , m₁ , m₂ , _) = rapp (relDel m₁ rf) (relDel m₂ ra)
relDel {k} m {ν} (rlam n fr rb) =
  rlam n
    (λ p l → Eq.transport (λ x → DifI x (bnd n)) (Eq.sym (del-as k ν p))
                          (fr (dlift k p) (mark-live→ m p l)))
    (relDel (O.mthere true m) rb)

-- WEAKENING
relIns : ∀ {k u v} (m : O.Mark false k u v) {ν : NameF}
         {a : L.Tm u} {e : RExpr}
       → Rel (del k ν) a e → Rel ν (O.insT m a) e
relIns m (rvar s)       = relVar (O.markF-Solo→ m s) (Eq.sym (del-soloAt→ m s _))
relIns m (rapp {sp = s} rf ra) with O.insSplit m s
... | (_ , _ , m₁ , m₂ , _) = rapp (relIns m₁ rf) (relIns m₂ ra)
relIns {k} m {ν} (rlam n fr rb) =
  rlam n
    (λ p l → let (p₀ , e , l₀) = mark-live← m p l
             in Eq.transport (λ z → DifI (ν z) (bnd n)) e
                  (Eq.transport (λ x → DifI x (bnd n)) (del-as k ν p₀) (fr p₀ l₀)))
    (relIns (O.mthere true m) rb)
