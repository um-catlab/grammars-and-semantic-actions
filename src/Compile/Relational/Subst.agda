{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SUBSTITUTION LEMMA, WHICH IS WHAT THE SQUARE WAS MISSING.

      relSubst :  Rel ν b b'  →  Rel (del k ν) a a'
               →  Rel (del k ν) (subSize m sp b a) (substE (ν k) a' b')

  `Compile.Relational.Refutation` shows the same statement with `≡` in
  place of `Rel` is FALSE.  This is the true one, and the difference is
  entirely in the conclusion's relation: the source contracts the usage
  (`del k`) and renames nothing, the target renames nothing and
  contracts nothing, and `Rel` absorbs the discrepancy because `rlam`
  does not care what level a binder carries.

  ------------------------------------------------------------------
  THE TWO SIDE CONDITIONS, AND WHY THEY ARE THE HONEST ONES
  ------------------------------------------------------------------

  `Eval.agda` states plainly that its substitution is naive, and gives
  the two reasons it is nevertheless safe here.  Both reappear as
  hypotheses, because both are load-bearing:

    Avoid k ν    the substituted position's name differs from every
                 other position's -- injectivity of the assignment,
                 weakened to the one position that matters.  This is
                 `Eval`'s reason (1), SCOPING.

    Empty u₂     the argument is CLOSED.  This is `Eval`'s reason (2),
                 call-by-value, and it is exactly what rules out
                 capture: `Opt.subS`'s `tlam` clause pushes the
                 argument under the residual binder (`insT mhere`), and
                 if the argument had a free name that binder could
                 catch it.  With no free names there is nothing to
                 catch.  Call-by-value only ever substitutes closed
                 values, so this costs nothing at the use site.

  What is NOT a hypothesis any more is "no binder of the body carries
  the substituted name".  That was assumed in the first version of this
  file; it is now DERIVED, because `Rel`'s `rlam` carries the
  non-shadowing premise and the substituted position is LIVE by
  `Mark true` (`markT-live`).  The improvement is not cosmetic -- the
  assumed form was unsatisfiable after evaluation (see `Base`'s header,
  and the `appLin appLin` measurement).

  ------------------------------------------------------------------
  `NotFree` MUST PERMIT SHADOWING
  ------------------------------------------------------------------

  `substE` STOPS at a binder that rebinds its own name, and stopping is
  correct: that binder shadows, so there is nothing below it to
  replace.  `NotFree` therefore reads

      NotFree x (rClos n b) = SameI x (bnd n) ⊎ NotFree x b

  -- "either this binder shadows `x`, or `x` is absent below".  A
  conjunctive reading would be simpler and would be false on the
  target's own values.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1.  `NotFree` is PRIMITIVE and marked.
-}
open import Cubical.Foundations.Prelude

module Compile.Relational.Subst where

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.LinToRust.Codegen
open import Compile.Relational.Base
open import Compile.Relational.Names
import TheoryGrammar.Instances.LinLam.Syntax as L
import TheoryGrammar.Instances.LinLam.Opt as O
import Compile.Semantics.Size as Sz

-- ==================================================================
-- §1  ABSENCE OF A NAME, UP TO SHADOWING.
-- ==================================================================

-- PRIMITIVE (phase 1)
NotFree : Ident → RExpr → Type₀
NotFree x (rVar y)       = DifI x y
NotFree x (rClos n b)    = SameI x (bnd n) ⊎ NotFree x b
NotFree x (rCall f a)    = NotFree x f × NotFree x a
NotFree x (rCtor _)      = Unit
NotFree x (rMatch s a b) = NotFree x s × (NotFree x a × NotFree x b)
NotFree x (rLet n e b)   = NotFree x e × (SameI x (bnd n) ⊎ NotFree x b)

-- ==================================================================
-- §2  WHAT `substE` DOES IN THE CASES THAT MATTER.
-- ==================================================================

ifE-diag : (c : Bool) (e : RExpr) → ifE c e e Eq.≡ e
ifE-diag true  e = Eq.refl
ifE-diag false e = Eq.refl

sameI-eq : (x y : Ident) → SameI x y → eqIdent x y Eq.≡ true
sameI-eq (bnd m) (bnd n) Eq.refl = eqIdent-refl (bnd m)
sameI-eq (fre m) (fre n) Eq.refl = eqIdent-refl (fre m)

-- it HITS
substE-hit : (x : Ident) (v : RExpr) → substE x v (rVar x) Eq.≡ v
substE-hit x v = Eq.ap (λ c → ifE c v (rVar x)) (eqIdent-refl x)

-- it goes UNDER a binder that is not its own name
substE-clos : (x : Ident) (v : RExpr) (n : ℕ) (b : RExpr)
            → DifI x (bnd n)
            → substE x v (rClos n b) Eq.≡ rClos n (substE x v b)
substE-clos x v n b d =
  Eq.ap (λ c → ifE c (rClos n b) (rClos n (substE x v b)))
        (eqIdent-dif x (bnd n) d)

-- ... and it is the IDENTITY where the name is absent or shadowed
substE-notFree : (x : Ident) (v : RExpr) (e : RExpr)
               → NotFree x e → substE x v e Eq.≡ e
substE-notFree x v (rVar y) nf =
  Eq.ap (λ c → ifE c v (rVar y)) (eqIdent-dif x y nf)
substE-notFree x v (rClos n b) (inl sm) =
  Eq.ap (λ c → ifE c (rClos n b) (rClos n (substE x v b)))
        (sameI-eq x (bnd n) sm)
substE-notFree x v (rClos n b) (inr nf) =
    Eq.ap (λ z → ifE (eqIdent x (bnd n)) (rClos n b) (rClos n z))
          (substE-notFree x v b nf)
  Eq.∙ ifE-diag (eqIdent x (bnd n)) (rClos n b)
substE-notFree x v (rCall f a) (nf , na) =
    Eq.ap (λ z → rCall z (substE x v a)) (substE-notFree x v f nf)
  Eq.∙ Eq.ap (rCall f) (substE-notFree x v a na)
substE-notFree x v (rCtor c) nf = Eq.refl
substE-notFree x v (rMatch s a b) (ns , (na , nb)) =
    Eq.ap (λ z → rMatch z (substE x v a) (substE x v b)) (substE-notFree x v s ns)
  Eq.∙ Eq.ap (λ z → rMatch s z (substE x v b)) (substE-notFree x v a na)
  Eq.∙ Eq.ap (rMatch s a) (substE-notFree x v b nb)
substE-notFree x v (rLet n e b) (ne , inl sm) =
    Eq.ap (λ z → rLet n z (ifE (eqIdent x (bnd n)) b (substE x v b)))
          (substE-notFree x v e ne)
  Eq.∙ Eq.ap (λ c → rLet n e (ifE c b (substE x v b))) (sameI-eq x (bnd n) sm)
substE-notFree x v (rLet n e b) (ne , inr nb) =
    Eq.ap (λ z → rLet n z (ifE (eqIdent x (bnd n)) b (substE x v b)))
          (substE-notFree x v e ne)
  Eq.∙ Eq.ap (λ z → rLet n e (ifE (eqIdent x (bnd n)) b z))
             (substE-notFree x v b nb)
  Eq.∙ Eq.ap (rLet n e) (ifE-diag (eqIdent x (bnd n)) b)

-- ==================================================================
-- §3  THE POSITION OF THE MARKED VARIABLE.
-- ==================================================================

markT-soloAt : ∀ {k u v} (m : O.Mark true k u v) (s : L.Solo v)
             → soloAt 0 v s Eq.≡ k
markT-soloAt O.mhere             s = Eq.refl
markT-soloAt (O.mthere true  m)  s = E.rec (O.markT-¬Empty m s)
markT-soloAt (O.mthere false m)  s =
  soloAt-shift 0 _ s Eq.∙ Eq.ap suc (markT-soloAt m s)

-- the marked position is LIVE -- which is what lets `rlam`'s
-- non-shadowing premise be applied AT it
markT-live : ∀ {k u v} (m : O.Mark true k u v) → LiveAt k v
markT-live O.mhere        = tt
markT-live (O.mthere c m) = markT-live m

markF-soloAt-dif : ∀ {k u v} (m : O.Mark false k u v) (s : L.Solo v)
                 → Dif (soloAt 0 v s) k
markF-soloAt-dif (O.mhere {u}) s =
  Eq.transport (λ z → Dif z 0) (Eq.sym (soloAt-shift 0 u s)) tt
markF-soloAt-dif (O.mthere true  m) s = tt
markF-soloAt-dif (O.mthere false m) s =
  Eq.transport (λ z → Dif z (suc _)) (Eq.sym (soloAt-shift 0 _ s))
    (markF-soloAt-dif m s)

-- with a CLOSED argument, every live position of the result came from
-- the body -- so `rlam`'s premise transports through the split
use⊎-liveL : ∀ {u₁ u₂ u} (sp : L.Use⊎ u₁ u₂ u) → L.Empty u₂
           → (p : ℕ) → LiveAt p u → LiveAt p u₁
use⊎-liveL L.unil        e p       l = l
use⊎-liveL (L.uleft sp)  e zero    l = tt
use⊎-liveL (L.uleft sp)  e (suc p) l = use⊎-liveL sp e p l
use⊎-liveL (L.uright sp) e p       l = E.rec e
use⊎-liveL (L.uskip sp)  e zero    l = l
use⊎-liveL (L.uskip sp)  e (suc p) l = use⊎-liveL sp e p l

-- ==================================================================
-- §4  AVOIDANCE: INJECTIVITY, WEAKENED TO THE ONE POSITION IN PLAY.
-- ==================================================================

Inj : NameF → Type₀
Inj ν = (p q : ℕ) → Dif p q → DifI (ν p) (ν q)

Avoid : ℕ → NameF → Type₀
Avoid k ν = (p : ℕ) → Dif p k → DifI (ν p) (ν k)

avoid-inj : {ν : NameF} → Inj ν → (k : ℕ) → Avoid k ν
avoid-inj inj k p d = inj p k d

avoid-ext : {k n : ℕ} {ν : NameF} → DifI (bnd n) (ν k) → Avoid k ν
          → Avoid (suc k) (ext n ν)
avoid-ext dn av zero    d = dn
avoid-ext dn av (suc p) d = av p d

-- `nameOf` is injective, so `Avoid` is free at the compiler's own
-- assignment
inj-ext : {n : ℕ} {ν : NameF} → Inj ν → ((p : ℕ) → DifI (ν p) (bnd n))
        → Inj (ext n ν)
inj-ext inj fr zero    zero    d = E.rec d
inj-ext inj fr zero    (suc q) d = difI-sym _ _ (fr q)
inj-ext inj fr (suc p) zero    d = fr p
inj-ext inj fr (suc p) (suc q) d = inj p q d

inj-nameOf : (d : ℕ) → Inj (nameOf d)
inj-nameOf zero    p q d = d
inj-nameOf (suc d) p q e = inj-ext (inj-nameOf d) (freshB-nameOf d) p q e

-- ==================================================================
-- §5  A DEAD SLOT'S NAME IS NOT FREE IN THE COMPILED BRANCH.
--
-- This is `Opt.subS`'s `tapp` clause seen from the target: the premise
-- the variable did NOT go to is `delT`-strengthened on the source, and
-- `substE` must leave it alone.  The `rlam` case CASES on whether the
-- binder shadows the name -- `NotFree` admits both outcomes, and
-- `substE` is the identity either way.
-- ==================================================================

relNotFree : ∀ {k u v} (m : O.Mark false k u v) {ν : NameF}
             {y : L.Tm v} {y' : RExpr}
           → Avoid k ν → Rel ν y y' → NotFree (ν k) y'
relNotFree m av (rvar s) =
  difI-sym _ _ (av _ (markF-soloAt-dif m s))
relNotFree m av (rapp {sp = s} rf ra) with O.delSplit m s
... | (_ , _ , m₁ , m₂ , _) = relNotFree m₁ av rf , relNotFree m₂ av ra
relNotFree {k} m {ν} av (rlam n fr rb) = go (eqIdent (ν k) (bnd n)) Eq.refl
  where
  go : (c : Bool) → eqIdent (ν k) (bnd n) Eq.≡ c → NotFree (ν k) (rClos n _)
  go true  e = inl (eqIdent-true _ _ e)
  go false e =
    inr (relNotFree (O.mthere true m)
           (avoid-ext (difI-sym _ _ (eqIdent-false _ _ e)) av) rb)

-- ==================================================================
-- §6  THE SUBSTITUTION LEMMA.
-- ==================================================================

relSubst : ∀ {k u₁ v u₂ u} (m : O.Mark true k u₁ v) (sp : L.Use⊎ u₁ u₂ u)
           {ν : NameF} {b : L.Tm v} {b' : RExpr}
           {a : L.Tm u₂} {a' : RExpr}
         → L.Empty u₂ → Avoid k ν
         → Rel ν b b' → Rel (del k ν) a a'
         → Rel (del k ν) (Sz.subSize m sp b a) (substE (ν k) a' b')

relSubst m sp emp av (rvar so) ra with markT-soloAt m so
... | Eq.refl =
  Eq.transport (λ z → Rel _ _ z) (Eq.sym (substE-hit _ _)) (relCoe _ ra)

relSubst {k} m sp {ν} emp av (rlam n fr rb) ra =
  Eq.transport (λ z → Rel _ _ z)
    (Eq.sym (substE-clos (ν k) _ n _ (fr k (markT-live m))))
    (rlam n
      (λ p l → Eq.transport (λ x → DifI x (bnd n)) (Eq.sym (del-as k ν p))
                 (fr (dlift k p) (mark-live→ m p (use⊎-liveL sp emp p l))))
      (relSubst (O.mthere true m) (L.uleft sp) emp
                (avoid-ext (difI-sym _ _ (fr k (markT-live m))) av)
                rb (relIns O.mhere ra)))

relSubst m sp {ν} emp av (rapp {sp = s} rx ry) ra with O.atSplit m s
... | inl (_ , _ , mp , mq , sq) =
  rapp (relSubst mp (O.useExch sq sp .snd .fst) emp av rx ra)
       (Eq.transport (λ z → Rel _ _ z)
          (Eq.sym (substE-notFree (ν _) _ _ (relNotFree mq av ry)))
          (relDel mq ry))
... | inr (_ , _ , mp , mq , sq) =
  rapp (Eq.transport (λ z → Rel _ _ z)
          (Eq.sym (substE-notFree (ν _) _ _ (relNotFree mp av rx)))
          (relDel mp rx))
       (relSubst mq (O.useAssoc sq sp .snd .fst) emp av ry ra)
