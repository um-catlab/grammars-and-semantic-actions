{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE MEASURE `Opt.agda` WAS MISSING.

  `Instances/LinLam/Opt.agda` closes with an honest negative result:

      "Termination of a normaliser.  `foldTm` is one bottom-up sweep.
       Iterating to a normal form needs a decreasing measure, and the
       grading the framework supplies (`live`) is the WRONG one -- it
       increases under a binder.  So `hyloC`/`löb` are unavailable here
       and the passes are single-sweep by necessity, not by choice."

  Both halves of that are true, and the conclusion does not follow.
  `live` is the wrong measure; it does not follow that there is no
  measure.  This file supplies one, and the reason it exists is the
  reason the whole calculus exists.

  ------------------------------------------------------------------
  1.  IN A LINEAR CALCULUS, β STRICTLY DECREASES TERM SIZE.
  ------------------------------------------------------------------

  In the untyped λ-calculus β is not size-decreasing, and it is not
  even size-bounded: contracting `(λx. x x) t` produces `t t`, which is
  roughly twice the size of `t`.  That is DUPLICATION, and duplication
  is exactly what the index rules out.  `Use⊎` has no clause taking
  `true` on both sides (`Context.noDupUse`), so the bound variable of a
  `tlam` occurs EXACTLY ONCE in its body, and therefore

      size (b[a/x])  +  1  =  size b  +  size a                (★)

  -- one occurrence of `x`, of size 1, is replaced by one copy of `a`.
  The `+ 1` on the left is the occurrence that went away.  There is no
  inequality here and no case analysis on how often `x` occurs: (★) is
  an EQUATION, and it is an equation because the calculus is linear.

  Contracting a redex then removes a `tlam` and a `tapp` on top of that
  and duplicates nothing:

      size ((λx.b) a)  =  1 + (1 + size b) + size a
                       =  size (b[a/x]) + 3.

  So β decreases the size by exactly three, and the linear λ-calculus
  is strongly normalising for an almost trivial reason -- no reducibility
  candidates, no logical relation, no types at all.  `Normalise.agda`
  turns that into a terminating recursion.

  ------------------------------------------------------------------
  2.  WHERE LINEARITY IS ACTUALLY USED, AND HOW TO SEE IT.
  ------------------------------------------------------------------

  It is used in exactly one place, and it is worth making that place
  visible rather than leaving it as an artefact of a typing rule.

  `Opt.subT`'s `tapp` clause dispatches on `atSplit`, whose codomain is
  a DISJOINT SUM

      atSplit : Mark true n u v → Use⊎ v₁ v₂ v
              → (marked variable in the LEFT premise)
              ⊎ (marked variable in the RIGHT premise)

  and the substituted argument follows the marked variable into
  whichever premise it went to.  Because the sum is a `⊎` and not a
  `×`, the argument is placed once.  §2 below proves the sharp form:

      markT-both : Mark true n p v₁ → Mark true n q v₂
                 → Use⊎ v₁ v₂ v → ⊥

  -- the marked variable CANNOT be live in both halves of a splitting.
  This is `Context.noDupUse` generalised away from the diagonal, and
  `noDupUse` is recovered from it in one line, so the dependence is
  literal rather than moral.  In a cartesian calculus `atSplit` would
  have to return `(L ⊎ R) ⊎ (L × R)`, the third summand would place a
  SECOND copy of the argument, and (★) would degrade to the inequality
  `size (b[a/x]) ≤ size b * size a`, which is not a measure.

  ------------------------------------------------------------------
  3.  WHY THE STATEMENT IS ABOUT `subS` AND NOT ABOUT `subT`.
  ------------------------------------------------------------------

  (★) is stated below as an intrinsic property of a substitution
  `subS` whose motive IS the equation:

      subS : Mark true n u₁ v → Use⊎ u₁ u₂ u → (b : Tm v) (a : Tm u₂)
           → Σ[ t ∈ Tm u ] (suc ∣ t ∣ ≡ ∣ b ∣ + ∣ a ∣)

  This is the house idiom -- `Quicksort`'s `Spec`, `Opt.Budget`'s
  "occurrences = live + binders": the motive of the recursion is the
  statement being proved, so the algebra produces the invariant as it
  computes and there is nothing left to re-check.  `subS` is `Opt.subT`
  clause for clause; only the codomain is bigger.

  It is ALSO forced, and the reason is worth recording because it is a
  general fact about this kind of development.  `subT`'s `tapp` clause
  reads

      subT m sp (tapp s a b) arg = go (atSplit m s)
        where go (inl …) = … ; go (inr …) = …

  so `subT m sp (tapp s a b) arg` reduces to a `where`-lifted function
  applied to the NEUTRAL term `atSplit m s`.  A propositional statement
  about it cannot be proved by `with atSplit m s`: with-abstraction
  abstracts occurrences of the scrutinee in the GOAL, the goal does not
  mention `atSplit m s`, so nothing is abstracted and case-splitting on
  the with-variable teaches the type-checker nothing.  There is no
  `inspect` idiom that helps, because the obstruction is that `go` is
  inaccessible, not that the equation is missing.  Hence: put the
  invariant in the motive, or reprove nothing at all.  The moral is the
  one `Quicksort` already makes, arrived at from the other side.

  ------------------------------------------------------------------
  4.  WHAT IS IN HERE
  ------------------------------------------------------------------

    §1   `size`, as a fold at the constant motive `SizeG _ = ℕ`.  One
         `foldTm`, three lines of algebra, and the three computation
         rules hold by `refl` -- so nothing downstream ever unfolds it.
    §2   `markT-both`, and `noDupUse` as its corollary.
    §3   `size` is invariant under the three index manipulations
         (`coeTm`, `insT`, `delT`).  All three are one-line inductions
         and all three are needed by (★).
    §4   `subS`, and (★) as its second component.
    §5   the β step in the form `Normalise.agda` consumes:
         `size (redex) ≡ size (contractum) + 3`.
-}
open import Cubical.Foundations.Prelude

module Compile.Semantics.Size where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.LinLam.Opt public

-- ==================================================================
-- §1  SIZE, AS A FOLD.
--
-- The motive is the constant grammar `Δ ℕ` -- `SizeG u = ℕ` -- so
-- `size : TmG ⊢ SizeG` is a term of the calculus and the recursion is
-- `Opt.foldTm`, the ONE structural recursion on `Tm` in the
-- development.  Nothing new is matched here.
-- ==================================================================

SizeG : Ctx
SizeG _ = ℕ

-- a variable is one node
sizeVarA : SoloG ⊢ SizeG
sizeVarA u _ = 1

-- an application is one node plus its two premises.  `⊛-E'` reads the
-- two slots off `boolΠ`; the splitting itself is discarded, which is
-- the whole reason the size of an application is a SUM and not a max.
sizeAppA : (SizeG ⊛ SizeG) ⊢ SizeG
sizeAppA = ⊛-E' SizeG SizeG λ u u₁ u₂ s m n → suc (m + n)

-- a binder is one node plus its body, at the EXTENDED usage
sizeLamA : BodyOf SizeG ⊢ SizeG
sizeLamA u n = suc n

sizeAlg : StepG SizeG ⊢ SizeG
sizeAlg = ⊕-E sizeVarA (⊕-E sizeAppA sizeLamA)

size : TmG ⊢ SizeG
size = foldTm SizeG sizeAlg

∣_∣ : ∀ {u} → Tm u → ℕ
∣_∣ {u} t = size u t

-- ------------------------------------------------------------------
-- The three computation rules.  All `refl`: `⊛-mk`/`⊛-E'` cancel
-- definitionally because `boolΠ` is applied at a CONSTANT arity in
-- both, which is precisely what `Opt.§2` exists to arrange.  Every
-- proof below cites these instead of unfolding `foldTm`.
-- ------------------------------------------------------------------

size-var : ∀ {u} (so : Solo u) → ∣ tvar so ∣ ≡ 1
size-var _ = refl

size-app : ∀ {u₁ u₂ u} (s : Use⊎ u₁ u₂ u) (a : Tm u₁) (b : Tm u₂)
         → ∣ tapp s a b ∣ ≡ suc (∣ a ∣ + ∣ b ∣)
size-app _ _ _ = refl

size-lam : ∀ {u} (b : Tm (true ∷ u)) → ∣ tlam b ∣ ≡ suc ∣ b ∣
size-lam _ = refl

-- every term has at least one node -- needed to know a redex is not of
-- size zero, hence that the recursion in `Normalise.agda` is grounded
size-pos : ∀ {u} (t : Tm u) → Σ[ n ∈ ℕ ] (∣ t ∣ ≡ suc n)
size-pos (tvar so)     = 0 , refl
size-pos (tapp s a b)  = ∣ a ∣ + ∣ b ∣ , refl
size-pos (tlam b)      = ∣ b ∣ , refl

-- ==================================================================
-- §2  LINEARITY, IN THE FORM (★) NEEDS IT.
--
-- `Context.noDupUse` says a usage that owns a variable does not split
-- as ITSELF twice.  What substitution needs is the same fact off the
-- diagonal: the variable BEING SUBSTITUTED FOR -- the one carried by a
-- `Mark true n` -- cannot be live in both halves of a splitting.
-- ==================================================================

-- PRIMITIVE (phase 1): THE EXCLUSION.  Every clause is forced; the only
-- one that does any work is the first, and it is the missing
-- `(true,true)` constructor of `Use⊎` and nothing else.
markT-both : ∀ {n p q v v₁ v₂}
           → Use⊎ v₁ v₂ v → Mark true n p v₁ → Mark true n q v₂ → ⊥
markT-both unil       ()                 _
markT-both (uleft  s) mhere              ()
markT-both (uleft  s) (mthere .true  m₁) (mthere .false m₂) = markT-both s m₁ m₂
markT-both (uright s) (mthere .false m₁) (mthere .true  m₂) = markT-both s m₁ m₂
markT-both (uskip  s) (mthere .false m₁) (mthere .false m₂) = markT-both s m₁ m₂

-- ... and `noDupUse` is the diagonal instance, recovered in one line.
-- The dependence of (★) on linearity is therefore literal: remove the
-- missing constructor and this file's headline equation is false.
noDupUse' : (u : Usage) → Use⊎ (true ∷ u) (true ∷ u) (true ∷ u) → ⊥
noDupUse' u s = markT-both s mhere mhere

-- ==================================================================
-- §3  SIZE IS BLIND TO THE INDEX MANIPULATIONS.
--
-- `coeTm` transports along an `Eq`-equation of usages, `insT` inserts
-- an unused variable and `delT` removes one.  None of the three touch
-- the tree, so none of them touch the size -- but `subT` uses all
-- three, so all three equations are on (★)'s critical path.
-- ==================================================================

-- `coeTm` matches `Eq.refl`, so this is not a `subst` and it reduces
size-coe : ∀ {u v} (e : u Eq.≡ v) (t : Tm u) → ∣ coeTm e t ∣ ≡ ∣ t ∣
size-coe Eq.refl t = refl

size-ins : ∀ {n u v} (m : Mark false n u v) (t : Tm u) → ∣ insT m t ∣ ≡ ∣ t ∣
size-ins m (tvar so)    = refl
size-ins m (tapp s a b) = cong suc (cong₂ _+_ (size-ins _ a) (size-ins _ b))
size-ins m (tlam b)     = cong suc (size-ins _ b)

size-del : ∀ {n u v} (m : Mark false n u v) (t : Tm v) → ∣ delT m t ∣ ≡ ∣ t ∣
size-del m (tvar so)    = refl
size-del m (tapp s a b) = cong suc (cong₂ _+_ (size-del _ a) (size-del _ b))
size-del m (tlam b)     = cong suc (size-del _ b)

-- ==================================================================
-- §4  SUBSTITUTION, WITH (★) IN THE MOTIVE.
--
-- `subS` is `Opt.subT` clause for clause; the second component is the
-- equation the clause makes true.  See the header §3 for why the
-- equation cannot instead be proved ABOUT `subT`.
-- ==================================================================

private
  -- (b + y) + a  =  1 + (t + y)      given   1 + t = b + a
  -- -- the argument travelled into the LEFT premise
  shuffleL : (X Y A T : ℕ) → suc T ≡ X + A → (X + Y) + A ≡ suc (T + Y)
  shuffleL X Y A T e =
      sym (+-assoc X Y A)
    ∙ cong (X +_) (+-comm Y A)
    ∙ +-assoc X A Y
    ∙ cong (_+ Y) (sym e)

  -- ... and into the RIGHT premise
  shuffleR : (X Y A T : ℕ) → suc T ≡ Y + A → (X + Y) + A ≡ suc (X + T)
  shuffleR X Y A T e =
      sym (+-assoc X Y A)
    ∙ cong (X +_) (sym e)
    ∙ +-suc X T

-- PRIMITIVE (phase 1): LINEAR SUBSTITUTION, SIZED.
--
--   tvar   the body IS the marked variable, so the argument is the
--          answer; `1 + ∣arg∣ = ∣tvar∣ + ∣arg∣` because a variable has
--          size one -- this is the clause (★)'s `+ 1` comes from.
--   tapp   `atSplit` says the variable went to exactly ONE premise
--          (§2), the argument follows it, and the OTHER premise is
--          merely strengthened (`delT`), so its size is unchanged.
--          Nothing is duplicated and the arithmetic is a reassociation.
--   tlam   go under the binder; the argument is shifted past it
--          (`insT`), which again does not change its size.
subS : ∀ {n u₁ v u₂ u} → Mark true n u₁ v → Use⊎ u₁ u₂ u
     → (b : Tm v) (a : Tm u₂)
     → Σ[ t ∈ Tm u ] (suc ∣ t ∣ ≡ ∣ b ∣ + ∣ a ∣)

subS m sp (tvar so) arg =
    coeTm (useEmptyL sp (markT-Solo m so)) arg
  , cong suc (size-coe _ arg)

subS {n} {u₁} {_} {u₂} {u} m sp (tapp {v₁} {v₂} s x y) arg = go (atSplit m s)
  where
  Out : Type₀
  Out = Σ[ t ∈ Tm u ] (suc ∣ t ∣ ≡ ∣ tapp s x y ∣ + ∣ arg ∣)

  go : ((Σ[ p ∈ Usage ] Σ[ q ∈ Usage ]
           (Mark true n p v₁ × Mark false n q v₂ × Use⊎ p q u₁))
      ⊎ (Σ[ p ∈ Usage ] Σ[ q ∈ Usage ]
           (Mark false n p v₁ × Mark true n q v₂ × Use⊎ p q u₁)))
     → Out
  go (inl (p , q , mp , mq , sq)) =
    let (t , l , r) = useExch sq sp
        (x' , e)    = subS mp l x arg
    in tapp r x' (delT mq y)
     , cong (λ z → suc (suc (∣ x' ∣ + z))) (size-del mq y)
     ∙ cong suc (sym (shuffleL (∣ x ∣) (∣ y ∣) (∣ arg ∣) (∣ x' ∣) e))
  go (inr (p , q , mp , mq , sq)) =
    let (t , l , r) = useAssoc sq sp
        (y' , e)    = subS mq l y arg
    in tapp r (delT mp x) y'
     , cong (λ z → suc (suc (z + ∣ y' ∣))) (size-del mp x)
     ∙ cong suc (sym (shuffleR (∣ x ∣) (∣ y ∣) (∣ arg ∣) (∣ y' ∣) e))

subS m sp (tlam b) arg =
  let (t , e) = subS (mthere true m) (uleft sp) b (insT mhere arg)
  in tlam t
   , cong suc e ∙ cong (λ z → suc (∣ b ∣ + z)) (size-ins mhere arg)

-- the underlying map, and the equation, separately
subSize : ∀ {n u₁ v u₂ u} (m : Mark true n u₁ v) (sp : Use⊎ u₁ u₂ u)
        → (b : Tm v) (a : Tm u₂) → Tm u
subSize m sp b a = subS m sp b a .fst

-- ------------------------------------------------------------------
-- (★).  THE HEADLINE.  Substitution is size-ADDITIVE, on the nose.
--
-- Read the `suc` on the left as the occurrence of the bound variable
-- that was consumed.  In a cartesian calculus the corresponding
-- statement is an inequality with a multiplicative bound, and it is
-- not a termination measure.
-- ------------------------------------------------------------------
substSize : ∀ {n u₁ v u₂ u} (m : Mark true n u₁ v) (sp : Use⊎ u₁ u₂ u)
          → (b : Tm v) (a : Tm u₂)
          → suc ∣ subSize m sp b a ∣ ≡ ∣ b ∣ + ∣ a ∣
substSize m sp b a = subS m sp b a .snd

-- ... as a term of the calculus, at the type `Opt.substT` has.  This is
-- `Opt.substT`'s recursion; only the motive of the recursion differs.
substTS : (BodyOf TmG ⊛ TmG) ⊢ TmG
substTS = ⊛-E' (BodyOf TmG) TmG λ u u₁ u₂ s b a → subSize mhere s b a

-- ==================================================================
-- §5  β STRICTLY DECREASES SIZE.
--
-- The redex `(λx.b) a` has a `tapp` and a `tlam` that the contractum
-- does not, and by (★) the contractum is one node SHORTER than the two
-- premises together.  Three nodes, exactly, and no case analysis.
-- ==================================================================

betaSize : ∀ {u₁ u₂ u} (s : Use⊎ u₁ u₂ u) (b : Tm (true ∷ u₁)) (a : Tm u₂)
         → ∣ tapp s (tlam b) a ∣ ≡ suc (suc (suc ∣ subSize mhere s b a ∣))
betaSize s b a = cong (λ z → suc (suc z)) (sym (substSize mhere s b a))

-- ==================================================================
-- §6  IT COMPUTES.
-- ==================================================================

_ : ∣ idLin ∣ ≡ 2
_ = refl

_ : ∣ selfApp ∣ ≡ 5
_ = refl

_ : ∣ etaRedex ∣ ≡ 8
_ = refl

_ : ∣ betaEtaRedex ∣ ≡ 5
_ = refl

-- β on `selfApp = (λx.x) (λx.x)` : 5 ↦ 2, i.e. exactly three nodes
_ : ∣ subSize mhere unil (tvar tt) idLin ∣ ≡ 2
_ = refl

_ : subSize mhere unil (tvar tt) idLin ≡ idLin
_ = refl
