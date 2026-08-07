{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE AFFINE PROMODEL: OWNERSHIP, AND WHAT ONE CONSTRUCTOR COSTS.

  `Instances/LinLam/Context` presents linear contexts as a partial
  commutative monoid over `Usage = List Bool`, and its header names the
  load-bearing fact: what makes the promodel LINEAR is a constructor
  that is ABSENT.

      data Use⊎ : Usage → Usage → Usage → Type₀ where
        unil   : Use⊎ [] [] []
        uleft  : Use⊎ u v w → Use⊎ (true  ∷ u) (false ∷ v) (true  ∷ w)
        uright : Use⊎ u v w → Use⊎ (false ∷ u) (true  ∷ v) (true  ∷ w)
        uskip  : Use⊎ u v w → Use⊎ (false ∷ u) (false ∷ v) (false ∷ w)

  There is no `(true , true)` clause, so a variable cannot be used
  twice; and there is no `(false , false , true)` clause, so a variable
  that is OWNED cannot go unclaimed.  The first absence is no
  contraction.  The SECOND is no weakening, and it is the one Rust does
  not want: a value may be moved, or it may simply fall out of scope and
  be dropped.  So the ownership discipline of a Rust fragment is `Use⊎`
  with exactly one constructor restored:

        adrop  : Aff⊎ u v w → Aff⊎ (false ∷ u) (false ∷ v) (true  ∷ w)

  -- a live resource claimed by NEITHER premise.  Everything below is
  the consequence of that one line, and the point of the file is to say
  precisely which of the linear theorems survive it.

  ------------------------------------------------------------------
  THE TABLE.  Each cell names the theorem in this directory that backs
  it, or says honestly that it is not done.

                  LINEAR  (LinLam)        AFFINE  (here)          CARTESIAN (here)
  --------------  ----------------------  ----------------------  ----------------------
  contraction     REFUTED                 REFUTED                 HOLDS
                  `Context.noDupUse`      `noDupAff`, and the     `cboth`, `cdiag`;
                  (missing constructor)   sharper `affDiag`:      `lin⊂aff⊂cart` shows
                                          `Aff⊎ u u w → Empty u`  the inclusion is STRICT
  --------------  ----------------------  ----------------------  ----------------------
  weakening       REFUTED                 HOLDS                   HOLDS
                  `Contrast.noWkLin`      `wkUnit : ⊤G ⊢ 𝟙 ⊛ 𝟙`   (a fortiori; not
                  (`Use⊎` with both       `affWk : Free A ⊢        separately proved)
                  slots `Empty` forces    Own (⇓ A)`, and `⇓`
                  the whole `Empty`)      is a nontrivial monad
  --------------  ----------------------  ----------------------  ----------------------
  dead code       VACUOUS                 REAL                    REAL
                  `Opt.deadBinder :`      `Dead.deadWitness` and  (a fortiori; not
                  `DeadBinder ⊢ ⊥G`       `Dead.noDeadEmpty`      separately proved)
                                          refute it; the DCE
                                          pass has real content
                                          (`Dead.dceNotUnique`)
  --------------  ----------------------  ----------------------  ----------------------
  grading         HOLDS                   HOLDS                   REFUTED
  (`deg<`)        `Context.liveSplit`     `liveSplit≤` -- the     `cartNoProper`: for
                  is an EQUATION          equation degrades to    EVERY grading, the
                  `live u + live v ≡`     an INEQUALITY, and      diagonal splitting has
                  `live w`                that is still enough    no proper slot
  --------------  ----------------------  ----------------------  ----------------------
  budget          `occ ≡ live + lam`      `occ ≤ live + lam`      not done
  invariant       (`Opt.budgetEq`)        (`Dead.budgetLe`); the
                                          `≥` half is REFUTED
                                          (`Dead.noBudgetGe`)

  ------------------------------------------------------------------
  WHY THE GRADING SURVIVES, AND WHY THAT IS NOT OBVIOUS.

  `Context.liveSplit` is an equation:  live u + live v ≡ live w.  It is
  what makes `linGrading` work, and `adrop` destroys it -- the whole has
  a live variable neither part has.  What replaces it is

      liveSplit≤ :  live u + live v  ≤  live w

  and reading `deg≤`/`deg<` again shows this is all they ever needed:
  `deg≤` wants `live u ≤ live w`, which follows from `live u ≤ live u +
  live v` and the inequality; `deg<` wants `live u < live w` when the
  SIBLING is live, which follows from `live u < live u + live v` and the
  inequality.  Both uses were already one-sided.  So affinity makes the
  degree drop FASTER, and `Ind`/`Guard`/`hyloC` remain available
  verbatim.  Losing resources is not a problem for a well-founded
  recursion; only GAINING them is.

  That is the whole content of the "grading" row, and it is worth
  contrasting with the cartesian case at the bottom of this file, where
  the diagonal `Cart⊎ u u u` makes a slot equal to the whole and NO
  grading -- not merely `live` -- can have a proper slot there.  The
  three columns are therefore: an equation, an inequality, and nothing.

  ------------------------------------------------------------------
  WEAKENING IS A MONAD, NOT A RULE.

  The naive reading of "affine = weakening" would be `A ⊗ 𝟙 ⊢ A` with 𝟙
  terminal.  That is NOT what `adrop` gives, and the difference is
  instructive.  Write

      ⇓ A  =  A ⊛ 𝟙            (𝟙 = ⊗ˢ nilop, "nothing is owned")

  Unfolding, `⇓ A w` is `Σ[ u ] (u ⊑ w) × A u` up to the choice of the
  discarded complement -- `Syntax.⇓→WkG` / `Syntax.WkG→⇓` are the two
  maps; they are NOT proved inverse here, because the complement of a
  drop is only determined up to `Empty`, and nothing below needs it.
  So: a payload at a SMALLER usage, together with the resources it is
  entitled to discard.  Then

      ⇓-unit  : A ⊢ ⇓ A                 (holds linearly too -- unit law)
      ⇓-mult  : ⇓ (⇓ A) ⊢ ⇓ A           (transitivity of ⊑)

  so `⇓` is a monad, and LINEARLY it is the identity monad: `Use⊎` with
  an `Empty` slot forces the other slot to be the whole (`Opt.useEmptyR`),
  so `⇓ A ⊢ A` and the monad is trivial.  Affinely it is NOT: `𝟙-not-⇓-alg`
  refutes `⇓ 𝟙 ⊢ 𝟙`.  A grammar for which `⇓ A ⊢ A` DOES hold is exactly
  an algebra for the monad -- an "affine grammar" -- and `Syntax.atmAffine`
  is the statement that the affine terms form one, by `tdrop`.

  So the right slogan is not "weakening is available" but

      weakening is available FOR THE GRAMMARS THAT ADMIT IT, and `⇓`
      is the free such grammar.

  which is also the honest reading of Rust: `Drop` is a trait, not a
  structural rule, and a type that does not implement it (a linear
  resource, a `MutexGuard`-shaped thing) is not weakenable.

  ------------------------------------------------------------------
  WHAT `⊛` LOSES.  The right unit law `A ⊛ 𝟙 ⊢ A` is exactly what fails
  -- that is `⇓ A ⊢ A` again -- so `⊛` is only LAX unital here.  This is
  not a defect of the presentation: it is the same fact as "not every
  type is droppable", seen at the connective instead of at the monad.

  ------------------------------------------------------------------
  PRIMITIVE (matching the representation): `Empty`, `Solo`, `_⊑_`,
  `zeros`, `live`, `Aff⊎`, `AffSplit`, `AffParts`, `boolΠ`, and the
  `⊛`-interface (`⊛-mk`, `⊛-E'`, `⊛-map`, `⊛-dist*`).  Everything after
  §5 is a term of the calculus.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Affine.Base where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid public
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Graded

-- ==================================================================
-- §0  USAGES.  Verbatim `Context.agda`: position n says whether
-- variable n is still OWNED by this subterm.  Deliberately not
-- imported, so that nothing in §1-§5 depends on a file another agent
-- may be editing; the linear side is quarantined in `Contrast.agda`.
-- ==================================================================

Usage : Type₀
Usage = List Bool

none : ℕ → Usage
none zero    = []
none (suc n) = false ∷ none n

only : ℕ → ℕ → Usage
only zero    (suc n) = true  ∷ none n
only (suc i) (suc n) = false ∷ only i n
only _       zero    = []

-- "nothing is owned", recursively -- Unit/⊥-valued, hence definitionally
-- propositional, which is what keeps `refl` tests reducing
Empty : Usage → Type₀
Empty []          = Unit
Empty (true  ∷ _) = ⊥
Empty (false ∷ u) = Empty u

-- "exactly one variable is owned"
Solo : Usage → Type₀
Solo []          = ⊥
Solo (true  ∷ u) = Empty u
Solo (false ∷ u) = Solo u

-- the all-unowned usage of the same scope
zeros : Usage → Usage
zeros []      = []
zeros (_ ∷ u) = false ∷ zeros u

zerosEmpty : (u : Usage) → Empty (zeros u)
zerosEmpty []      = tt
zerosEmpty (_ ∷ u) = zerosEmpty u

-- ==================================================================
-- §1  THE AFFINE SPLITTING.
--
-- `Use⊎` plus `adrop`.  Read the four inherited constructors as the
-- linear discipline and `adrop` as the ownership one: the whole is
-- responsible for a variable that NEITHER premise claims, so it is
-- dropped at this node.
--
-- Still absent: any clause taking `true` on both sides.  That absence
-- is no-contraction, and it is what makes affine strictly weaker than
-- cartesian (§6).
-- ==================================================================

data Aff⊎ : Usage → Usage → Usage → Type₀ where
  anil   : Aff⊎ [] [] []
  aleft  : ∀ {u v w} → Aff⊎ u v w → Aff⊎ (true  ∷ u) (false ∷ v) (true  ∷ w)
  aright : ∀ {u v w} → Aff⊎ u v w → Aff⊎ (false ∷ u) (true  ∷ v) (true  ∷ w)
  askip  : ∀ {u v w} → Aff⊎ u v w → Aff⊎ (false ∷ u) (false ∷ v) (false ∷ w)
  -- THE ONE NEW CONSTRUCTOR.  A live resource claimed by neither
  -- premise: dropped here.
  adrop  : ∀ {u v w} → Aff⊎ u v w → Aff⊎ (false ∷ u) (false ∷ v) (true  ∷ w)

AffSplit : (o : MonOp) → Usage → Type₀
AffSplit nilop u = Empty u
AffSplit appop u = Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ] Aff⊎ u₁ u₂ u

-- the dependent eliminator for the `Bool` arity, as in `Heap/Base` and
-- `LinLam/Context`: ONE place where `true`/`false` are matched, so no
-- extended lambda is ever written and nominal mismatch cannot arise.
boolΠ : ∀ {ℓ} {M : Bool → Type ℓ} → M true → M false → (b : Bool) → M b
boolΠ t f true  = t
boolΠ t f false = f

AffParts : (o : MonOp) (u : Usage) → AffSplit o u → MonAr o → Usage
AffParts nilop u sp ()
AffParts appop u (u₁ , u₂ , _) = boolΠ u₁ u₂

affFib : Fibered monoidSig ℓ-zero ℓ-zero
affFib .carrier _ = Usage
affFib .Split     = AffSplit
affFib .parts     = AffParts

open RulesF affFib public

Ctx : Type₁
Ctx = TheoryTy ℓ-zero tt

-- AFFINE APPLICATION is the tensor; `𝟙` is the (only lax) unit.
_⊛_ : Ctx → Ctx → Ctx
A ⊛ B = ⊗ˢ appop (boolΠ A B)

infixr 20 _⊛_

𝟙 : Ctx
𝟙 = ⊗ˢ nilop (λ ())

-- ==================================================================
-- §2  NO CONTRACTION.  This is the half of linearity that affine KEEPS,
-- and it is the sharp statement that affine sits strictly BELOW
-- cartesian.  `Context.noDupUse` is the linear version; the second
-- theorem here is strictly stronger than anything stated there.
-- ==================================================================

-- PRIMITIVE (phase 1): `Context.noDupUse`, verbatim -- the (true,true)
-- clause is still missing, `adrop` did not add it.
noDupAff : (u : Usage) → Aff⊎ (true ∷ u) (true ∷ u) (true ∷ u) → ⊥
noDupAff u ()

-- THEOREM (the sharp form).  ONLY A DEAD USAGE SPLITS AS ITSELF.
--
-- `Opt.noSelfSplit` needs the hypothesis `0 < live u`; here the
-- conclusion is `Empty u` for an ARBITRARY whole `w`, which is both
-- stronger and hypothesis-free.  Every constructor with `true` in the
-- first slot has `false` in the second, so the diagonal can only be
-- built from `askip` and `adrop` -- and both of those leave the parts
-- unowned.  Affinity added a way to LOSE a resource, not to copy one.
affDiag : ∀ {u w} → Aff⊎ u u w → Empty u
affDiag anil       = tt
affDiag (askip s)  = affDiag s
affDiag (adrop s)  = affDiag s

-- ==================================================================
-- §3  THE GRADING.  `deg` still counts owned variables; the additivity
-- EQUATION of `Context.liveSplit` degrades to an INEQUALITY, and that
-- is exactly enough.
-- ==================================================================

live : Usage → ℕ
live []          = 0
live (true  ∷ u) = suc (live u)
live (false ∷ u) = live u

liveEmpty : (u : Usage) → Empty u → live u ≡ 0
liveEmpty []          _ = refl
liveEmpty (false ∷ u) e = liveEmpty u e

-- the sharp form of §2, in the shape `Opt.noSelfSplit` states it
noSelfSplitAff : (u : Usage) → 0 < live u → Aff⊎ u u u → ⊥
noSelfSplitAff u p s = ¬-<-zero (subst (0 <_) (liveEmpty u (affDiag s)) p)

-- PRIMITIVE (phase 1):  THE REPLACEMENT FOR `Context.liveSplit`.
--
-- Linearly this is `live u + live v ≡ live w`.  `adrop` is the one
-- clause where the two sides genuinely differ, and it is exactly the
-- clause that turns the equation into an inequality: the whole gained a
-- live variable that no part has.
liveSplit≤ : ∀ {u v w} → Aff⊎ u v w → live u + live v ≤ live w
liveSplit≤ anil        = ≤-refl
liveSplit≤ (aleft s)   = suc-≤-suc (liveSplit≤ s)
liveSplit≤ (aright {u} {v} {w} s) =
  subst (_≤ suc (live w)) (sym (+-suc (live u) (live v)))
        (suc-≤-suc (liveSplit≤ s))
liveSplit≤ (askip s)   = liveSplit≤ s
liveSplit≤ (adrop s)   = ≤-suc (liveSplit≤ s)         -- <-- THE ONE LOSSY CLAUSE

private
  weak : (a b : ℕ) → a ≤ a + b
  weak a b = b , +-comm b a

  strict : (a b : ℕ) → 0 < b → a < a + b
  strict a zero    p = E.rec (¬-<-zero p)
  strict a (suc b) _ = subst (suc a ≤_) (sym (+-suc a b)) (suc-≤-suc (weak a b))

affGrading : Grading affFib
affGrading .deg _ = live

affGrading .Proper nilop u sp ()
affGrading .Proper appop u (u₁ , u₂ , _) b = 0 < live (boolΠ {M = λ _ → Usage} u₂ u₁ b)

-- `deg≤`:  live (slot) ≤ live (slot) + live (sibling) ≤ live (whole).
-- Only the SECOND step changed, and it changed from `≡` to `≤`.
affGrading .deg≤ nilop u sp ()
affGrading .deg≤ appop u (u₁ , u₂ , s) =
  boolΠ {M = λ a → live (boolΠ {M = λ _ → Usage} u₁ u₂ a) ≤ live u}
        (≤-trans (weak (live u₁) (live u₂)) (liveSplit≤ s))
        (≤-trans (subst (live u₂ ≤_) (+-comm (live u₂) (live u₁))
                        (weak (live u₂) (live u₁)))
                 (liveSplit≤ s))

-- `deg<`:  a live sibling makes the step strict, and the inequality
-- carries it the rest of the way.
affGrading .deg< nilop u sp ()
affGrading .deg< appop u (u₁ , u₂ , s) =
  boolΠ {M = λ a → 0 < live (boolΠ {M = λ _ → Usage} u₂ u₁ a)
                 → live (boolΠ {M = λ _ → Usage} u₁ u₂ a) < live u}
        (λ pr → <≤-trans (strict (live u₁) (live u₂) pr) (liveSplit≤ s))
        (λ pr → <≤-trans
                  (subst (live u₂ <_) (+-comm (live u₂) (live u₁))
                         (strict (live u₂) (live u₁) pr))
                  (liveSplit≤ s))

affGraded : GradedFib monoidSig ℓ-zero ℓ-zero
affGraded = graded affFib affGrading

-- ==================================================================
-- §4  THE ⊛-INTERFACE, once.
--
-- `Opt.agda` writes these for the linear promodel and may not be
-- edited, so they are re-derived here.  Writing them ONCE is the point:
-- every extended lambda over `Bool` would otherwise be a fresh nominal
-- function that fails to reduce against the others.
-- ==================================================================

-- PRIMITIVE (phase 1): intro for `⊛`
⊛-mk : (A B : Ctx) (u u₁ u₂ : Usage) → Aff⊎ u₁ u₂ u → A u₁ → B u₂ → (A ⊛ B) u
⊛-mk A B u u₁ u₂ s x y =
  ⊗ˢ-I appop {A = boolΠ A B} u (u₁ , u₂ , s)
    (boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} A B a
                        (affFib .parts appop u (u₁ , u₂ , s) a)} x y)

-- PRIMITIVE (phase 1): elim for `⊛`
⊛-E' : (A B : Ctx) {C : Ctx}
     → ((u u₁ u₂ : Usage) → Aff⊎ u₁ u₂ u → A u₁ → B u₂ → C u)
     → (A ⊛ B) ⊢ C
⊛-E' A B {C} f = ⊗ˢ-E appop {A = boolΠ A B} {B = C}
  (λ u sp k → f u (sp .fst) (sp .snd .fst) (sp .snd .snd) (k true) (k false))

⊛-map : {A A' B B' : Ctx} → A ⊢ A' → B ⊢ B' → (A ⊛ B) ⊢ (A' ⊛ B')
⊛-map {A} {A'} {B} {B'} f g =
  ⊗ˢ-map appop {A = boolΠ A B} {B = boolΠ A' B'}
    (boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} A B a
                    ⊢ boolΠ {M = λ _ → Ctx} A' B' a} f g)

-- PRIMITIVE (phase 1): `⊗ˢ` is a Σ, so it distributes over `⊕`.
⊛-distR : (A B C : Ctx) → (A ⊛ (B ⊕ C)) ⊢ ((A ⊛ B) ⊕ (A ⊛ C))
⊛-distR A B C = ⊛-E' A (B ⊕ C) go
  where
  go : (u u₁ u₂ : Usage) → Aff⊎ u₁ u₂ u → A u₁ → (B ⊕ C) u₂
     → ((A ⊛ B) ⊕ (A ⊛ C)) u
  go u u₁ u₂ s x (inl y) = inl (⊛-mk A B u u₁ u₂ s x y)
  go u u₁ u₂ s x (inr z) = inr (⊛-mk A C u u₁ u₂ s x z)

⊛-distL : (A B C : Ctx) → ((A ⊕ B) ⊛ C) ⊢ ((A ⊛ C) ⊕ (B ⊛ C))
⊛-distL A B C = ⊛-E' (A ⊕ B) C go
  where
  go : (u u₁ u₂ : Usage) → Aff⊎ u₁ u₂ u → (A ⊕ B) u₁ → C u₂
     → ((A ⊛ C) ⊕ (B ⊛ C)) u
  go u u₁ u₂ s (inl x) z = inl (⊛-mk A C u u₁ u₂ s x z)
  go u u₁ u₂ s (inr y) z = inr (⊛-mk B C u u₁ u₂ s y z)

-- the unit, as a payload
𝟙-mk : {u : Usage} → Empty u → 𝟙 u
𝟙-mk e = e , λ ()

𝟙-Empty : {u : Usage} → 𝟙 u → Empty u
𝟙-Empty = fst

-- ==================================================================
-- §5  WEAKENING.
--
-- What affinity BUYS, in three increasingly internal forms.
-- ==================================================================

-- ------------------------------------------------------------------
-- 5.1  The drop order.  `u ⊑ v` -- "v owns everything u owns, and
-- possibly more".  Unit/⊥-valued, hence a proposition definitionally,
-- so a `tdrop` node carries no content and `refl` tests still reduce.
-- ------------------------------------------------------------------

infix 4 _⊑_

_⊑_ : Usage → Usage → Type₀                       -- PRIMITIVE
[]            ⊑ []            = Unit
[]            ⊑ (_ ∷ _)       = ⊥
(_ ∷ _)       ⊑ []            = ⊥
(true  ∷ u) ⊑ (true  ∷ v)     = u ⊑ v
(true  ∷ u) ⊑ (false ∷ v)     = ⊥
(false ∷ u) ⊑ (true  ∷ v)     = u ⊑ v
(false ∷ u) ⊑ (false ∷ v)     = u ⊑ v

⊑-refl : (u : Usage) → u ⊑ u
⊑-refl []          = tt
⊑-refl (true  ∷ u) = ⊑-refl u
⊑-refl (false ∷ u) = ⊑-refl u

⊑-trans : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
⊑-trans {[]}          {[]}          {[]}          p q = tt
⊑-trans {[]}          {[]}          {_ ∷ _}       p q = E.rec q
⊑-trans {[]}          {_ ∷ _}       {_}           p q = E.rec p
⊑-trans {_ ∷ _}       {[]}          {_}           p q = E.rec p
⊑-trans {_ ∷ _}       {_ ∷ _}       {[]}          p q = E.rec q
⊑-trans {true  ∷ u} {true  ∷ v} {true  ∷ w} p q = ⊑-trans p q
⊑-trans {true  ∷ u} {true  ∷ v} {false ∷ w} p q = E.rec q
⊑-trans {true  ∷ u} {false ∷ v} {_ ∷ _}     p q = E.rec p
⊑-trans {false ∷ u} {true  ∷ v} {true  ∷ w} p q = ⊑-trans p q
⊑-trans {false ∷ u} {true  ∷ v} {false ∷ w} p q = E.rec q
⊑-trans {false ∷ u} {false ∷ v} {true  ∷ w} p q = ⊑-trans p q
⊑-trans {false ∷ u} {false ∷ v} {false ∷ w} p q = ⊑-trans p q

⊑-live : ∀ {u v} → u ⊑ v → live u ≤ live v
⊑-live {[]}          {[]}          p = ≤-refl
⊑-live {[]}          {_ ∷ _}       p = E.rec p
⊑-live {_ ∷ _}       {[]}          p = E.rec p
⊑-live {true  ∷ u} {true  ∷ v} p = suc-≤-suc (⊑-live p)
⊑-live {true  ∷ u} {false ∷ v} p = E.rec p
⊑-live {false ∷ u} {true  ∷ v} p = ≤-suc (⊑-live p)
⊑-live {false ∷ u} {false ∷ v} p = ⊑-live p

-- ------------------------------------------------------------------
-- 5.2  Splittings with an EMPTY complement are exactly `⊑`.  Both
-- directions; `split→⊑` is where `adrop` earns its keep and `aright` is
-- absurd.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1)
split→⊑ : ∀ {u z v} → Aff⊎ u z v → Empty z → u ⊑ v
split→⊑ anil      e = tt
split→⊑ (aleft  s) e = split→⊑ s e
split→⊑ (aright s) e = E.rec e
split→⊑ (askip  s) e = split→⊑ s e
split→⊑ (adrop  s) e = split→⊑ s e

-- PRIMITIVE (phase 1)
⊑→split : ∀ {u v} → u ⊑ v → Aff⊎ u (zeros v) v
⊑→split {[]}          {[]}          p = anil
⊑→split {[]}          {_ ∷ _}       p = E.rec p
⊑→split {_ ∷ _}       {[]}          p = E.rec p
⊑→split {true  ∷ u} {true  ∷ v} p = aleft (⊑→split p)
⊑→split {true  ∷ u} {false ∷ v} p = E.rec p
⊑→split {false ∷ u} {true  ∷ v} p = adrop (⊑→split p)
⊑→split {false ∷ u} {false ∷ v} p = askip (⊑→split p)

-- the unit law that DOES hold, linearly and affinely alike
affUnitR : (u : Usage) → Aff⊎ u (zeros u) u
affUnitR []          = anil
affUnitR (true  ∷ u) = aleft (affUnitR u)
affUnitR (false ∷ u) = askip (affUnitR u)

-- THE AFFINE AXIOM, at the index.  EVERYTHING can be thrown away.  In
-- `Use⊎` this is refuted (`Contrast.noWkLin`): a splitting with both
-- slots `Empty` forces the whole to be `Empty`.
affDropAll : (u : Usage) → Aff⊎ (zeros u) (zeros u) u
affDropAll []          = anil
affDropAll (true  ∷ u) = adrop (affDropAll u)
affDropAll (false ∷ u) = askip (affDropAll u)

-- ------------------------------------------------------------------
-- 5.3  ... and internally.  From here everything is a `⊢`-term.
-- ------------------------------------------------------------------

-- THE HEADLINE.  Weakening as a term of the calculus, with no
-- hypothesis at all on the usage.  This is the internal `⊗ˢ`-level
-- statement of "a resource may be dropped".
wkUnit : ⊤G ⊢ (𝟙 ⊛ 𝟙)
wkUnit u _ = ⊛-mk 𝟙 𝟙 u (zeros u) (zeros u) (affDropAll u)
               (𝟙-mk (zerosEmpty u)) (𝟙-mk (zerosEmpty u))

-- ------------------------------------------------------------------
-- 5.4  THE WEAKENING MONAD.
--
--     ⇓ A w  ≅  Σ[ u ] (u ⊑ w) × A u
--
-- LINEARLY `⇓` is the identity (an `Empty` slot forces the other slot
-- to be the whole); affinely it is not, and `𝟙-not-⇓-alg` proves it.
-- ------------------------------------------------------------------

⇓ : Ctx → Ctx
⇓ A = A ⊛ 𝟙

-- unit: keep everything.  This direction holds LINEARLY too -- it is
-- the right unit law, and it is not what affinity buys.
⇓-unit : (A : Ctx) → A ⊢ ⇓ A
⇓-unit A u x = ⊛-mk A 𝟙 u u (zeros u) (affUnitR u) x (𝟙-mk (zerosEmpty u))

-- multiplication: two successive drops are one drop.  `⊑-trans`.
⇓-mult : (A : Ctx) → ⇓ (⇓ A) ⊢ ⇓ A
⇓-mult A = ⊛-E' (⇓ A) 𝟙 λ v p q s inner e →
  ⊛-mk A 𝟙 v (inner .fst .fst) (zeros v)
    (⊑→split (⊑-trans (split→⊑ (inner .fst .snd .snd)
                               (𝟙-Empty (inner .snd false)))
                      (split→⊑ s (𝟙-Empty e))))
    (inner .snd true)
    (𝟙-mk (zerosEmpty v))

⇓-map : {A B : Ctx} → A ⊢ B → ⇓ A ⊢ ⇓ B
⇓-map f = ⊛-map f idg

-- "A is AFFINE" = A is an algebra for the weakening monad = A's
-- inhabitants may be regarded as owning more than they use.  This is
-- Rust's `Drop`, and it is a PROPERTY of a grammar, not a rule of the
-- logic.
Affine : Ctx → Type₀
Affine A = ⇓ A ⊢ A

-- the general weakening map, for an affine grammar: `u ⊑ v → A u → A v`
affWeaken : {A : Ctx} → Affine A → ∀ {u v} → u ⊑ v → A u → A v
affWeaken {A} alg {u} {v} p x =
  alg v (⊛-mk A 𝟙 v u (zeros v) (⊑→split p) x (𝟙-mk (zerosEmpty v)))

-- ------------------------------------------------------------------
-- 5.5  NOT EVERY GRAMMAR IS AFFINE.  `𝟙` is the counterexample, and it
-- is the sharpest one available: the unit of the tensor is not its own
-- weakening-closure, so `⊛` is only LAX unital.
-- ------------------------------------------------------------------

-- a point of `⇓ 𝟙` at a usage that OWNS something
⇓𝟙-pt : (⇓ 𝟙) (true ∷ [])
⇓𝟙-pt = ⊛-mk 𝟙 𝟙 (true ∷ []) (false ∷ []) (false ∷ []) (adrop anil)
          (𝟙-mk tt) (𝟙-mk tt)

-- ... but `𝟙 (true ∷ [])` is `Empty (true ∷ [])`, i.e. `⊥`
𝟙-not-⇓-alg : Affine 𝟙 → ⊥
𝟙-not-⇓-alg alg = 𝟙-Empty (alg (true ∷ []) ⇓𝟙-pt)

-- COROLLARY.  The right unit law of `⊛` FAILS affinely.  (It holds
-- linearly -- `Opt.useEmptyR`.)
no-⊛-unitR : ((A : Ctx) → (A ⊛ 𝟙) ⊢ A) → ⊥
no-⊛-unitR f = 𝟙-not-⇓-alg (f 𝟙)

-- ------------------------------------------------------------------
-- 5.6  Weakening at the head bit, in the reindexed shape `lamT` uses.
-- `Own A` is `Opt.BodyOf A`; `Free A` is the same scope with the head
-- variable NOT owned.
-- ------------------------------------------------------------------

Own : Ctx → Ctx
Own A u = A (true ∷ u)

Free : Ctx → Ctx
Free A u = A (false ∷ u)

-- THE AFFINE RULE, as a `⊢`-term at a reindexed motive: a grammar that
-- does not own the head variable can be made to own it, at the cost of
-- a discarded unit.  For an AFFINE grammar the `⇓` disappears
-- (`Syntax.dropT`).
affWk : (A : Ctx) → Free A ⊢ Own (⇓ A)
affWk A u x =
  ⊛-mk A 𝟙 (true ∷ u) (false ∷ u) (false ∷ zeros u)
    (adrop (affUnitR u)) x (𝟙-mk (zerosEmpty u))

-- ==================================================================
-- §6  THE THIRD COLUMN: THE CARTESIAN PROMODEL, AND WHY IT HAS NO
-- GRADING.
--
-- One more constructor -- `cboth`, contraction -- and the whole
-- inductive layer collapses.  This is the `Instances/Group/NoGrading`
-- move localised to a single constructor: not "this particular grading
-- fails" but "no grading has a proper slot at the diagonal", hence no
-- `hyloC`, no `löb`, no structural recursion on an application.
-- ==================================================================

data Cart⊎ : Usage → Usage → Usage → Type₀ where
  cnil   : Cart⊎ [] [] []
  cleft  : ∀ {u v w} → Cart⊎ u v w → Cart⊎ (true  ∷ u) (false ∷ v) (true  ∷ w)
  cright : ∀ {u v w} → Cart⊎ u v w → Cart⊎ (false ∷ u) (true  ∷ v) (true  ∷ w)
  cskip  : ∀ {u v w} → Cart⊎ u v w → Cart⊎ (false ∷ u) (false ∷ v) (false ∷ w)
  cdrop  : ∀ {u v w} → Cart⊎ u v w → Cart⊎ (false ∷ u) (false ∷ v) (true  ∷ w)
  -- CONTRACTION.  The clause `Use⊎` and `Aff⊎` both refuse.
  cboth  : ∀ {u v w} → Cart⊎ u v w → Cart⊎ (true  ∷ u) (true  ∷ v) (true  ∷ w)

CartSplit : (o : MonOp) → Usage → Type₀
CartSplit nilop u = Empty u
CartSplit appop u = Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ] Cart⊎ u₁ u₂ u

CartParts : (o : MonOp) (u : Usage) → CartSplit o u → MonAr o → Usage
CartParts nilop u sp ()
CartParts appop u (u₁ , u₂ , _) = boolΠ u₁ u₂

cartFib : Fibered monoidSig ℓ-zero ℓ-zero
cartFib .carrier _ = Usage
cartFib .Split     = CartSplit
cartFib .parts     = CartParts

-- the three promodels, strictly nested.  (`Use⊎ ⊆ Aff⊎` is in
-- `Contrast.agda`, which is the only file that touches `LinLam`.)
aff→cart : ∀ {u v w} → Aff⊎ u v w → Cart⊎ u v w
aff→cart anil       = cnil
aff→cart (aleft s)  = cleft  (aff→cart s)
aff→cart (aright s) = cright (aff→cart s)
aff→cart (askip s)  = cskip  (aff→cart s)
aff→cart (adrop s)  = cdrop  (aff→cart s)

-- ... and STRICTLY: contraction is a cartesian splitting that is not
-- affine.  This is `noDupAff` read as a separation result.
aff⊊cart : Cart⊎ (true ∷ []) (true ∷ []) (true ∷ [])
         × (Aff⊎ (true ∷ []) (true ∷ []) (true ∷ []) → ⊥)
aff⊊cart = cboth cnil , noDupAff []

-- the diagonal: EVERY usage splits as itself twice
cdiag : (u : Usage) → Cart⊎ u u u
cdiag []          = cnil
cdiag (true  ∷ u) = cboth (cdiag u)
cdiag (false ∷ u) = cskip (cdiag u)

private
  boolΠ-diag : ∀ {ℓ} {X : Type ℓ} (x : X) (a : Bool)
             → boolΠ {M = λ _ → X} x x a ≡ x
  boolΠ-diag x = boolΠ {M = λ a → boolΠ {M = λ _ → _} x x a ≡ x} refl refl

-- THEOREM.  NO GRADING OF THE CARTESIAN PROMODEL HAS A PROPER SLOT AT
-- THE DIAGONAL.
--
-- Not "`live` is not a grading" -- `deg = const 0`, `Proper = ⊥` is
-- always a legal `Grading`, exactly as `Group/NoGrading`'s header
-- insists.  The statement is a rigidity one: the diagonal splitting
-- makes a slot EQUAL to the whole, so `deg< ` is unsatisfiable there,
-- for every degree whatsoever.  Recursion on a cartesian application
-- cannot descend, and `Guard`/`hyloC` are unavailable, because the
-- premise they need is refuted.
cartNoProper : (G : Grading cartFib) (u : Usage) (a : Bool)
             → G .Proper appop u (u , u , cdiag u) a → ⊥
cartNoProper G u a pr =
  ¬m<m (subst (λ z → G .deg tt z < G .deg tt u)
              (boolΠ-diag u a)
              (G .deg< appop u (u , u , cdiag u) a pr))

-- ... and the same fact stated as "the affine grading does not
-- transport": `liveSplit≤` is FALSE for `Cart⊎`.
cartNoLiveSplit : ((u v w : Usage) → Cart⊎ u v w → live u + live v ≤ live w) → ⊥
cartNoLiveSplit f =
  ¬m<m (f (true ∷ []) (true ∷ []) (true ∷ []) (cboth cnil))
