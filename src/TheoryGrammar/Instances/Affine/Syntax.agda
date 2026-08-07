{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  AFFINE TERMS OVER THE OWNERSHIP PROMODEL -- a Rust fragment.

  `LinLam/Syntax` reads the linear typing rules off `⊗ˢ` and reindexing:

      appT : (Tm ⊛ Tm) ⊢ Tm            application  =  the tensor
      lamT : (λ u → Tm (true ∷ u)) ⊢ Tm   abstraction  =  reindexing

  Both survive here unchanged -- `⊛` is now `⊗ˢ appop` over `Aff⊎`, so
  its type still says "the context splits", and `_⊢_` still preserves
  the usage.  What is NEW is a fourth rule, and it is the whole of
  affinity:

      dropT : Free ATmG ⊢ Own ATmG

  "a term that does not own the head variable may be given it".  In
  Rust this is the fact that a binding whose value is never moved out is
  still well-formed: the value is dropped at the end of the scope.  In
  `LinLam` no such term exists, and `Contrast.noWkLin` says why.

  ------------------------------------------------------------------
  WHY `tdrop` IS A CONSTRUCTOR AND NOT A THEOREM.

  One might hope weakening were derivable, as `Opt.insT` (shifting) is.
  It is not, and the reason is at the leaves: `tvar : Solo u → Tm u`
  pins the usage to exactly one live variable, and no amount of
  restructuring turns a `Solo` usage into a bigger one.  Weakening has
  to be a term former -- exactly as `Drop` in Rust is a trait
  implementation and not a consequence of the type system.

  It is a term former carrying a PROPOSITION (`_⊑_` is Unit/⊥-valued),
  so it costs no computational content and the `refl` tests at the end
  of this file still reduce.

  ------------------------------------------------------------------
  ... AND IT IS EXACTLY THE MONAD ALGEBRA.

  `Base` builds `⇓ A = A ⊛ 𝟙`, the weakening monad, and proves that not
  every grammar is an algebra for it (`𝟙-not-⇓-alg`).  Here

      atmAffine : Affine ATmG          -- i.e. ⇓ ATmG ⊢ ATmG

  says the affine terms ARE one, and `dropT` is then not a primitive at
  all but a composite of `Base.affWk` with that algebra structure
  (`dropT-is-tdrop`).  So the file has exactly one new primitive,
  `tdrop`, and everything else is phase 2.

  PRIMITIVE (phase 1): `appT`, `lamT`, `varT`, `wkT`, `unroll`,
  `foldATm`, `⊑-isProp`.  Everything else is a `⊢`-composite.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Affine.Syntax where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Affine.Base public

private variable ℓA ℓB : Level

-- ==================================================================
-- §0  NOTATION -- `Own`/`Free` come from `Base`; `under` is the
-- functorial action of the head-reindexing, as in `Opt.agda`.
-- ==================================================================

SoloG : Ctx
SoloG u = Solo u

-- the premise-grammar of the weakening rule: a payload at a SMALLER
-- usage, plus the entitlement.  `⇓` is the same thing built out of `⊛`.
WkG : Ctx → Ctx
WkG A v = Σ[ u ∈ Usage ] ((u ⊑ v) × A u)

-- PRIMITIVE (phase 1): reindexing along `u ↦ true ∷ u` is functorial
under : {A B : Ctx} → A ⊢ B → Own A ⊢ Own B
under f u = f (true ∷ u)

-- PRIMITIVE (phase 1): `_⊑_` is Unit/⊥-valued, hence a proposition, so
-- a `tdrop` node has no content to choose.  This is what makes the
-- weakening rule free rather than a source of ambiguity.
⊑-isProp : (u v : Usage) (p q : u ⊑ v) → p ≡ q
⊑-isProp []          []          p q = refl
⊑-isProp []          (_ ∷ _)     p q = E.rec p
⊑-isProp (_ ∷ _)     []          p q = E.rec p
⊑-isProp (true  ∷ u) (true  ∷ v)     = ⊑-isProp u v
⊑-isProp (true  ∷ u) (false ∷ v) p q = E.rec p
⊑-isProp (false ∷ u) (true  ∷ v)     = ⊑-isProp u v
⊑-isProp (false ∷ u) (false ∷ v)     = ⊑-isProp u v

-- ==================================================================
-- §1  THE TERMS.  Three linear rules, plus `tdrop`.
-- ==================================================================

data ATm : Usage → Type₀ where
  tvar  : ∀ {u} → Solo u → ATm u
  tapp  : ∀ {u₁ u₂ u} → Aff⊎ u₁ u₂ u → ATm u₁ → ATm u₂ → ATm u
  tlam  : ∀ {u} → ATm (true ∷ u) → ATm u
  -- WEAKENING.  Not present in `LinLam.Tm`.
  tdrop : ∀ {u v} → u ⊑ v → ATm u → ATm v

ATmG : Ctx
ATmG = ATm

-- ==================================================================
-- §2  THE TYPING RULES, as terms of the calculus.
-- ==================================================================

-- PRIMITIVE (phase 1): application is the tensor -- `⊛` IS the side
-- condition `Γ = Γ₁ ⊎ Γ₂`, and now it also permits `Γ` to own more
-- than `Γ₁ ⊎ Γ₂` does, which is `adrop`.
appT : (ATmG ⊛ ATmG) ⊢ ATmG
appT u ((u₁ , u₂ , s) , k) = tapp s (k true) (k false)

-- PRIMITIVE (phase 1): abstraction is reindexing along weakening
lamT : Own ATmG ⊢ ATmG
lamT u t = tlam t

-- PRIMITIVE (phase 1)
varT : SoloG ⊢ ATmG
varT u s = tvar s

-- PRIMITIVE (phase 1): THE AFFINE RULE
wkT : WkG ATmG ⊢ ATmG
wkT v (u , p , t) = tdrop p t

-- ==================================================================
-- §3  `WkG` IS `⇓`, so the affine rule is the monad algebra.
--
-- Both directions are `Base`'s `split→⊑` / `⊑→split`; nothing new is
-- proved here, which is the point -- the syntax's weakening rule and
-- the promodel's weakening monad are the same fact.
-- ==================================================================

⇓→WkG : (A : Ctx) → ⇓ A ⊢ WkG A
⇓→WkG A = ⊛-E' A 𝟙 λ v u₁ u₂ s x e → u₁ , split→⊑ s (𝟙-Empty e) , x

WkG→⇓ : (A : Ctx) → WkG A ⊢ ⇓ A
WkG→⇓ A v (u , p , x) =
  ⊛-mk A 𝟙 v u (zeros v) (⊑→split p) x (𝟙-mk (zerosEmpty v))

-- THEOREM.  The affine terms are an algebra for the weakening monad.
atmAffine : Affine ATmG
atmAffine = wkT ∘g ⇓→WkG ATmG

-- ... hence general weakening, `u ⊑ v → ATm u → ATm v`, with no
-- recursion on the term: it is one `tdrop`.
weakenT : ∀ {u v} → u ⊑ v → ATm u → ATm v
weakenT = affWeaken atmAffine

-- ------------------------------------------------------------------
-- 3.1  WEAKENING AT THE HEAD BIT, phase 2: `Base.affWk` followed by
-- the algebra, under the binder.  No pointful Agda.
-- ------------------------------------------------------------------

dropT : Free ATmG ⊢ Own ATmG
dropT = under atmAffine ∘g affWk ATmG

-- ... and it is `tdrop` at the reflexive entitlement.  The two proofs
-- of `(false ∷ u) ⊑ (true ∷ u)` differ syntactically and agree by
-- `⊑-isProp`; there is nothing else between them.
dropT-is-tdrop : (u : Usage) (t : ATm (false ∷ u))
               → dropT u t ≡ tdrop (⊑-refl u) t
dropT-is-tdrop u t = cong (λ p → tdrop p t) (⊑-isProp _ _ _ _)

-- ==================================================================
-- §4  THE RECURSOR.  Four summands now, one per rule.  As in
-- `Opt.agda` the recursion is genuinely primitive: `affGrading` grades
-- by `live`, and going under a binder makes `live` go UP.
-- ==================================================================

StepG : Ctx → Ctx
StepG A = SoloG ⊕ ((A ⊛ A) ⊕ (Own A ⊕ WkG A))

-- the four typing rules, as one algebra
roll : StepG ATmG ⊢ ATmG
roll = ⊕-E varT (⊕-E appT (⊕-E lamT wkT))

-- PRIMITIVE (phase 1)
unroll : ATmG ⊢ StepG ATmG
unroll u (tvar s)               = inl s
unroll u (tapp {u₁} {u₂} s a b) = inr (inl (⊛-mk ATmG ATmG u u₁ u₂ s a b))
unroll u (tlam b)               = inr (inr (inl b))
unroll u (tdrop {u₁} p t)       = inr (inr (inr (u₁ , p , t)))

-- PRIMITIVE (phase 1): THE recursion.
foldATm : (A : Ctx) → StepG A ⊢ A → ATmG ⊢ A
foldATm A α u (tvar s) = α u (inl s)
foldATm A α u (tapp {u₁} {u₂} s a b) =
  α u (inr (inl (⊛-mk A A u u₁ u₂ s (foldATm A α u₁ a) (foldATm A α u₂ b))))
foldATm A α u (tlam b)         = α u (inr (inr (inl (foldATm A α (true ∷ u) b))))
foldATm A α u (tdrop {u₁} p t) = α u (inr (inr (inr (u₁ , p , foldATm A α u₁ t))))

rollUnroll : (u : Usage) (t : ATm u) → roll u (unroll u t) ≡ t
rollUnroll u (tvar s)     = refl
rollUnroll u (tapp s a b) = refl
rollUnroll u (tlam b)     = refl
rollUnroll u (tdrop p t)  = refl

foldRoll : (u : Usage) (t : ATm u) → foldATm ATmG roll u t ≡ t
foldRoll u (tvar s)     = refl
foldRoll u (tapp s a b) = cong₂ (tapp s) (foldRoll _ a) (foldRoll _ b)
foldRoll u (tlam b)     = cong tlam (foldRoll _ b)
foldRoll u (tdrop p t)  = cong (tdrop p) (foldRoll _ t)

-- ==================================================================
-- §5  PASSES.  Same category as `LinLam`, same freeness argument: a
-- pass preserves the usage, so it cannot invent an owned variable.
-- What it CAN now do -- and could not linearly -- is discard one.
-- ==================================================================

Pass : Type₀
Pass = ATmG ⊢ ATmG

idPass : Pass
idPass = idg

_then_ : Pass → Pass → Pass
p then q = q ∘g p

infixl 5 _then_

foldRollPass : foldATm ATmG roll ≡ idPass
foldRollPass i u t = foldRoll u t i

-- ==================================================================
-- §6  TERMS.  The first two are linear; the rest are NOT, and each one
-- is a fact the linear calculus cannot state.
-- ==================================================================

-- `λx. x` -- linear, and its own linear counterpart
idAff : ATm []
idAff = tlam (tvar tt)

-- the same at a scope with one unowned variable
idAff0 : ATm (false ∷ [])
idAff0 = tlam (tvar tt)

-- `(λx.x) (λx.x)`
selfApp : ATm []
selfApp = tapp anil idAff idAff

-- ------------------------------------------------------------------
-- 6.1  THE AFFINE TERM.  `λx. λy. x` -- the K combinator.  Its inner
-- body owns `y` and does not use it, so it is `tdrop`ped.  There is no
-- `LinLam.Tm` of this shape, and `Contrast.noLinearK` says so via the
-- budget.
-- ------------------------------------------------------------------

constAff : ATm []
constAff = tlam (tlam (tdrop {false ∷ true ∷ []} {true ∷ true ∷ []} tt (tvar tt)))

-- ------------------------------------------------------------------
-- 6.2  A DEAD BINDER.  `λ_. (λx.x)`: the bound variable is owned by
-- the body and used by nothing.  This is the term `Opt.deadBinder`
-- proves cannot exist linearly, and `Dead.deadWitness` turns it into
-- the refutation.
-- ------------------------------------------------------------------

deadBody : Own ATmG []              -- i.e. ATm (true ∷ [])
deadBody = tdrop tt idAff0

deadLam : ATm []
deadLam = tlam deadBody

-- an application of it: the argument is genuinely dropped
deadApp : ATm []
deadApp = tapp anil deadLam idAff

-- ==================================================================
-- §7  IT COMPUTES.
-- ==================================================================

_ : idPass [] idAff ≡ idAff
_ = refl

_ : foldATm ATmG roll [] constAff ≡ constAff
_ = refl

_ : foldATm ATmG roll [] deadApp ≡ deadApp
_ = refl

-- weakening at the head bit, at a point
_ : dropT [] idAff0 ≡ tdrop tt idAff0
_ = refl

-- ... and general weakening, at a point
_ : weakenT {false ∷ []} {true ∷ []} tt idAff0 ≡ tdrop tt idAff0
_ = refl
