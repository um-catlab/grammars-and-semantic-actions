{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- PHASE 3. OPTIMISATION PASSES OVER THE LINEAR CALCULUS. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Opt where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_<_; ¬-<-zero)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.LinLam.Syntax public

private variable ℓA ℓB : Level

-- §0 NOTATION. `BodyOf A` is `A` pulled back along the weakening map `u ↦
-- true ∷ u` -- the Cartesian lift `Syntax.agda` already uses to type
-- `lamT`.

BodyOf : TheoryTy ℓA tt → TheoryTy ℓA tt
BodyOf A u = A (true ∷ u)

SoloG : Ctx
SoloG u = Solo u

-- PRIMITIVE (phase 1): reindexing is functorial.
under : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      → A ⊢ B → BodyOf A ⊢ BodyOf B
under f u = f (true ∷ u)

-- §1 THE INDEX ALGEBRA. Usages form a partial commutative monoid; the
-- passes need its associativity, its unit laws, and one fact about scope
-- extension.

-- 1.1 Unit laws. An `Empty` slot contributes nothing, so the other slot IS
-- the whole.

-- PRIMITIVE (phase 1)
useEmptyL : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → Empty u₁ → u₂ Eq.≡ u
useEmptyL unil       e = Eq.refl
useEmptyL (uleft  s) e = E.rec e
useEmptyL (uright s) e = Eq.ap (true  ∷_) (useEmptyL s e)
useEmptyL (uskip  s) e = Eq.ap (false ∷_) (useEmptyL s e)

-- PRIMITIVE (phase 1)
useEmptyR : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → Empty u₂ → u₁ Eq.≡ u
useEmptyR unil       e = Eq.refl
useEmptyR (uleft  s) e = Eq.ap (true  ∷_) (useEmptyR s e)
useEmptyR (uright s) e = E.rec e
useEmptyR (uskip  s) e = Eq.ap (false ∷_) (useEmptyR s e)

-- PRIMITIVE (phase 1): a `Solo` usage has exactly one live variable.
soloLive : (u : Usage) → Solo u → live u ≡ 1
soloLive (true  ∷ u) e = cong suc (emptyLive u e)
  where
  emptyLive : (v : Usage) → Empty v → live v ≡ 0
  emptyLive []          _ = refl
  emptyLive (false ∷ v) e = emptyLive v e
soloLive (false ∷ u) e = soloLive u e

-- 1.2 Associativity, in the two shapes the passes actually need.

-- PRIMITIVE (phase 1):  (p ⊎ q) ⊎ r  ↦  p ⊎ (q ⊎ r)
useAssoc : ∀ {p q pq r s} → Use⊎ p q pq → Use⊎ pq r s
         → Σ[ t ∈ Usage ] (Use⊎ q r t × Use⊎ p t s)
useAssoc unil        unil       = [] , unil , unil
useAssoc (uleft s₁)  (uleft s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (false ∷ t) , uskip  a , uleft  b
useAssoc (uright s₁) (uleft s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (true  ∷ t) , uleft  a , uright b
useAssoc (uskip s₁)  (uright s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (true  ∷ t) , uright a , uright b
useAssoc (uskip s₁)  (uskip s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (false ∷ t) , uskip  a , uskip  b

-- PRIMITIVE (phase 1):  (p ⊎ q) ⊎ r  ↦  (p ⊎ r) ⊎ q   (the exchange)
useExch : ∀ {p q pq r s} → Use⊎ p q pq → Use⊎ pq r s
        → Σ[ t ∈ Usage ] (Use⊎ p r t × Use⊎ t q s)
useExch unil        unil       = [] , unil , unil
useExch (uleft s₁)  (uleft s₂) =
  let (t , a , b) = useExch s₁ s₂ in (true  ∷ t) , uleft  a , uleft  b
useExch (uright s₁) (uleft s₂) =
  let (t , a , b) = useExch s₁ s₂ in (false ∷ t) , uskip  a , uright b
useExch (uskip s₁)  (uright s₂) =
  let (t , a , b) = useExch s₁ s₂ in (true  ∷ t) , uright a , uleft  b
useExch (uskip s₁)  (uskip s₂) =
  let (t , a , b) = useExch s₁ s₂ in (false ∷ t) , uskip  a , uskip  b

-- 1.3 MARKERS. `Mark b n u v` says `v` is `u` with the bit `b` inserted at
-- position `n`.

data Mark (b : Bool) : ℕ → Usage → Usage → Type₀ where
  mhere  : ∀ {u} → Mark b 0 u (b ∷ u)
  mthere : ∀ {n u v} (c : Bool) → Mark b n u v → Mark b (suc n) (c ∷ u) (c ∷ v)

-- PRIMITIVE (phase 1): an inserted `false` is invisible to `Empty`
markF-Empty→ : ∀ {n u v} → Mark false n u v → Empty u → Empty v
markF-Empty→ mhere            e = e
markF-Empty→ (mthere true  m) e = e
markF-Empty→ (mthere false m) e = markF-Empty→ m e

markF-Empty← : ∀ {n u v} → Mark false n u v → Empty v → Empty u
markF-Empty← mhere            e = e
markF-Empty← (mthere true  m) e = e
markF-Empty← (mthere false m) e = markF-Empty← m e

-- ... and to `Solo`
markF-Solo→ : ∀ {n u v} → Mark false n u v → Solo u → Solo v
markF-Solo→ mhere            s = s
markF-Solo→ (mthere true  m) s = markF-Empty→ m s
markF-Solo→ (mthere false m) s = markF-Solo→ m s

markF-Solo← : ∀ {n u v} → Mark false n u v → Solo v → Solo u
markF-Solo← mhere            s = s
markF-Solo← (mthere true  m) s = markF-Empty← m s
markF-Solo← (mthere false m) s = markF-Solo← m s

-- PRIMITIVE (phase 1): an inserted `true` is a live variable, so the
-- extended usage is never empty.  This is the clause that kills the
-- "the substituted variable is some OTHER variable" case below.
markT-¬Empty : ∀ {n u v} → Mark true n u v → Empty v → ⊥
markT-¬Empty mhere            e = e
markT-¬Empty (mthere true  m) e = e
markT-¬Empty (mthere false m) e = markT-¬Empty m e

markT-Solo : ∀ {n u v} → Mark true n u v → Solo v → Empty u
markT-Solo mhere            s = s
markT-Solo (mthere true  m) s = E.rec (markT-¬Empty m s)
markT-Solo (mthere false m) s = markT-Solo m s

-- PRIMITIVE (phase 1): a splitting survives inserting an unused
-- variable, in both directions.
insSplit : ∀ {n u v u₁ u₂} → Mark false n u v → Use⊎ u₁ u₂ u
         → Σ[ v₁ ∈ Usage ] Σ[ v₂ ∈ Usage ]
             (Mark false n u₁ v₁ × Mark false n u₂ v₂ × Use⊎ v₁ v₂ v)
insSplit mhere s = _ , _ , mhere , mhere , uskip s
insSplit (mthere true m) (uleft s) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in _ , _ , mthere true m₁ , mthere false m₂ , uleft s'
insSplit (mthere true m) (uright s) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in _ , _ , mthere false m₁ , mthere true m₂ , uright s'
insSplit (mthere false m) (uskip s) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in _ , _ , mthere false m₁ , mthere false m₂ , uskip s'

delSplit : ∀ {n u v v₁ v₂} → Mark false n u v → Use⊎ v₁ v₂ v
         → Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ]
             (Mark false n u₁ v₁ × Mark false n u₂ v₂ × Use⊎ u₁ u₂ u)
delSplit mhere (uskip s) = _ , _ , mhere , mhere , s
delSplit (mthere true m) (uleft s) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in _ , _ , mthere true m₁ , mthere false m₂ , uleft s'
delSplit (mthere true m) (uright s) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in _ , _ , mthere false m₁ , mthere true m₂ , uright s'
delSplit (mthere false m) (uskip s) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in _ , _ , mthere false m₁ , mthere false m₂ , uskip s'

-- PRIMITIVE (phase 1): THE LINEARITY LEMMA AT THE INDEX LEVEL.
atSplit : ∀ {n u v v₁ v₂} → Mark true n u v → Use⊎ v₁ v₂ v
        → (Σ[ p ∈ Usage ] Σ[ q ∈ Usage ]
             (Mark true n p v₁ × Mark false n q v₂ × Use⊎ p q u))
        ⊎ (Σ[ p ∈ Usage ] Σ[ q ∈ Usage ]
             (Mark false n p v₁ × Mark true n q v₂ × Use⊎ p q u))
atSplit mhere (uleft s)  = inl (_ , _ , mhere , mhere , s)
atSplit mhere (uright s) = inr (_ , _ , mhere , mhere , s)
atSplit (mthere true m) (uleft s) with atSplit m s
... | inl (p , q , m₁ , m₂ , s') =
        inl (_ , _ , mthere true m₁ , mthere false m₂ , uleft s')
... | inr (p , q , m₁ , m₂ , s') =
        inr (_ , _ , mthere true m₁ , mthere false m₂ , uleft s')
atSplit (mthere true m) (uright s) with atSplit m s
... | inl (p , q , m₁ , m₂ , s') =
        inl (_ , _ , mthere false m₁ , mthere true m₂ , uright s')
... | inr (p , q , m₁ , m₂ , s') =
        inr (_ , _ , mthere false m₁ , mthere true m₂ , uright s')
atSplit (mthere false m) (uskip s) with atSplit m s
... | inl (p , q , m₁ , m₂ , s') =
        inl (_ , _ , mthere false m₁ , mthere false m₂ , uskip s')
... | inr (p , q , m₁ , m₂ , s') =
        inr (_ , _ , mthere false m₁ , mthere false m₂ , uskip s')

-- §2 THE MULTIPLICATIVE INTERFACE, once. `⊛` is `⊗ˢ appop (boolΠ A B)`, so
-- its intro and elim are `⊗ˢ-I` and `⊗ˢ-E` with the arity family spelled
-- by `boolΠ`.

-- PRIMITIVE (phase 1): intro for `⊛`
⊛-mk : (A B : Ctx) (u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → A u₁ → B u₂ → (A ⊛ B) u
⊛-mk A B u u₁ u₂ s x y =
  ⊗ˢ-I appop {A = boolΠ A B} u (u₁ , u₂ , s)
    (boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} A B a
                        (linFib .parts appop u (u₁ , u₂ , s) a)} x y)

-- PRIMITIVE (phase 1): elim for `⊛` -- `⊗ˢ-E`'s `MultiHomˢ` with the
-- two slots read off by `boolΠ`'s computation rules.  This is `appE`
-- from `Syntax.agda`, generalised in the two grammars.
⊛-E' : (A B : Ctx) {C : Ctx}
     → ((u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → A u₁ → B u₂ → C u)
     → (A ⊛ B) ⊢ C
⊛-E' A B {C} f = ⊗ˢ-E appop {A = boolΠ A B} {B = C}
  (λ u sp k → f u (sp .fst) (sp .snd .fst) (sp .snd .snd) (k true) (k false))

-- the functorial action, slotwise -- `⊗ˢ-map` at `boolΠ`
⊛-map : {A A' B B' : Ctx} → A ⊢ A' → B ⊢ B' → (A ⊛ B) ⊢ (A' ⊛ B')
⊛-map {A} {A'} {B} {B'} f g =
  ⊗ˢ-map appop {A = boolΠ A B} {B = boolΠ A' B'}
    (boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} A B a
                    ⊢ boolΠ {M = λ _ → Ctx} A' B' a} f g)

-- NOT a primitive: a composite of `⊛-E'` and `⊛-mk`, i.e. of `⊗ˢ-E` and
-- `⊗ˢ-I`.  The general fact is `RulesFib.⊗ˢ-⊕ᴰ-out`; the binary form is
-- written out here only because matching it against `⊗ˢ o (λ a → ⊕ᴰ …)`
-- costs more arity-η coercion than the two clauses below.
⊛-distR : (A B C : Ctx) → (A ⊛ (B ⊕ C)) ⊢ ((A ⊛ B) ⊕ (A ⊛ C))
⊛-distR A B C = ⊛-E' A (B ⊕ C) go
  where
  go : (u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → A u₁ → (B ⊕ C) u₂
     → ((A ⊛ B) ⊕ (A ⊛ C)) u
  go u u₁ u₂ s x (inl y) = inl (⊛-mk A B u u₁ u₂ s x y)
  go u u₁ u₂ s x (inr z) = inr (⊛-mk A C u u₁ u₂ s x z)

⊛-distL : (A B C : Ctx) → ((A ⊕ B) ⊛ C) ⊢ ((A ⊛ C) ⊕ (B ⊛ C))
⊛-distL A B C = ⊛-E' (A ⊕ B) C go
  where
  go : (u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → (A ⊕ B) u₁ → C u₂
     → ((A ⊛ C) ⊕ (B ⊛ C)) u
  go u u₁ u₂ s (inl x) z = inl (⊛-mk A C u u₁ u₂ s x z)
  go u u₁ u₂ s (inr y) z = inr (⊛-mk B C u u₁ u₂ s y z)

-- §3 TERM PRIMITIVES. Four of them, and the recursor.

-- transport along an `Eq` equation of usages; reduces on `Eq.refl`,
-- which is why §1.1 produces `Eq.≡` and not a Path
coeTm : ∀ {u v} → u Eq.≡ v → Tm u → Tm v
coeTm Eq.refl t = t

-- PRIMITIVE (phase 1): SHIFTING -- an unused variable may be inserted
-- anywhere in the scope.  `⊢`-typed at `n = 0` as `TmG ⊢ BodyOf' TmG`
-- below; the general `n` is needed only to go under binders.
insT : ∀ {n u v} → Mark false n u v → Tm u → Tm v
insT m (tvar s)     = tvar (markF-Solo→ m s)
insT m (tapp s a b) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in tapp s' (insT m₁ a) (insT m₂ b)
insT m (tlam b)     = tlam (insT (mthere true m) b)

-- PRIMITIVE (phase 1): STRENGTHENING -- an unused variable may be removed.
delT : ∀ {n u v} → Mark false n u v → Tm v → Tm u
delT m (tvar s)     = tvar (markF-Solo← m s)
delT m (tapp s a b) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in tapp s' (delT m₁ a) (delT m₂ b)
delT m (tlam b)     = tlam (delT (mthere true m) b)

-- the two of them as terms of the calculus, at a reindexed motive --
-- the same shape as `lamT`
Unused : Ctx
Unused u = Tm (false ∷ u)

shiftT : TmG ⊢ Unused
shiftT u = insT mhere

strengthenT : Unused ⊢ TmG
strengthenT u = delT mhere

-- 3.1  The shape functor and the recursor.

StepG : Ctx → Ctx
StepG A = SoloG ⊕ ((A ⊛ A) ⊕ BodyOf A)

-- the three typing rules of `Syntax.agda`, as one algebra
roll : StepG TmG ⊢ TmG
roll = ⊕-E varT (⊕-E appT lamT)

-- PRIMITIVE (phase 1): ... and their joint inverse.  Downstream, no
-- pass ever matches on `Tm`; it uses `unroll` and `⊕-E`.
unroll : TmG ⊢ StepG TmG
unroll u (tvar s)               = inl s
unroll u (tapp {u₁} {u₂} s a b) = inr (inl (⊛-mk TmG TmG u u₁ u₂ s a b))
unroll u (tlam b)               = inr (inr b)

-- PRIMITIVE (phase 1): THE recursion.  `linGrading` cannot supply it
-- -- `deg = live` INCREASES under a binder -- so structural recursion
-- on `Tm` is genuinely primitive here, and it happens exactly once.
foldTm : (A : Ctx) → StepG A ⊢ A → TmG ⊢ A
foldTm A α u (tvar s) = α u (inl s)
foldTm A α u (tapp {u₁} {u₂} s a b) =
  α u (inr (inl (⊛-mk A A u u₁ u₂ s (foldTm A α u₁ a) (foldTm A α u₂ b))))
foldTm A α u (tlam b) = α u (inr (inr (foldTm A α (true ∷ u) b)))

-- `roll` and `unroll` are inverse -- definitionally in one direction
rollUnroll : (u : Usage) (t : Tm u) → roll u (unroll u t) ≡ t
rollUnroll u (tvar s)     = refl
rollUnroll u (tapp s a b) = refl
rollUnroll u (tlam b)     = refl

-- THEOREM. The identity pass is the fold of the typing rules.
foldRoll : (u : Usage) (t : Tm u) → foldTm TmG roll u t ≡ t
foldRoll u (tvar s)     = refl
foldRoll u (tapp s a b) = cong₂ (tapp s) (foldRoll _ a) (foldRoll _ b)
foldRoll u (tlam b)     = cong tlam (foldRoll _ b)

foldRollPass : foldTm TmG roll ≡ idPass
foldRollPass i u t = foldRoll u t i

-- 3.2  The two structural facts about a binder.

-- PRIMITIVE (phase 1): THE LINEARITY LEMMA.
freshSplit : BodyOf (TmG ⊛ TmG)
           ⊢ ((BodyOf TmG ⊛ TmG) ⊕ (TmG ⊛ BodyOf TmG))
freshSplit u ((v₁ , v₂ , s) , k) = go v₁ v₂ s (k true) (k false)
  where
  Cod : Ctx
  Cod = (BodyOf TmG ⊛ TmG) ⊕ (TmG ⊛ BodyOf TmG)

  go : (v₁ v₂ : Usage) → Use⊎ v₁ v₂ (true ∷ u) → Tm v₁ → Tm v₂ → Cod u
  go _ _ (uleft {u = w₁} {v = w₂} s') a b =
    inl (⊛-mk (BodyOf TmG) TmG u w₁ w₂ s' a (delT mhere b))
  go _ _ (uright {u = w₁} {v = w₂} s') a b =
    inr (⊛-mk TmG (BodyOf TmG) u w₁ w₂ s' (delT mhere a) b)

-- ... and its two inverses, so a pass that decides NOT to fire can
-- put the node back.  `insT` undoes the `delT` that `freshSplit` did.
unfreshL : (BodyOf TmG ⊛ TmG) ⊢ BodyOf (TmG ⊛ TmG)
unfreshL = ⊛-E' (BodyOf TmG) TmG λ u w₁ w₂ s a b →
  ⊛-mk TmG TmG (true ∷ u) (true ∷ w₁) (false ∷ w₂) (uleft s) a (insT mhere b)

unfreshR : (TmG ⊛ BodyOf TmG) ⊢ BodyOf (TmG ⊛ TmG)
unfreshR = ⊛-E' TmG (BodyOf TmG) λ u w₁ w₂ s a b →
  ⊛-mk TmG TmG (true ∷ u) (false ∷ w₁) (true ∷ w₂) (uright s) (insT mhere a) b

-- PRIMITIVE (phase 1): THE UNIT LAW, which is where η happens.
soloUnit : (TmG ⊛ BodyOf SoloG) ⊢ TmG
soloUnit = ⊛-E' TmG (BodyOf SoloG) λ u u₁ u₂ s f so →
  coeTm (useEmptyR s so) f

-- 3.3  Substitution -- the β step, and the file's headline type.

-- PRIMITIVE (phase 1): linear substitution.
subT : ∀ {n u₁ v u₂ u} → Mark true n u₁ v → Use⊎ u₁ u₂ u
     → Tm v → Tm u₂ → Tm u
subT m sp (tvar so) arg = coeTm (useEmptyL sp (markT-Solo m so)) arg
subT m sp (tapp s a b) arg = go (atSplit m s)
  where
  go : _ → Tm _
  go (inl (p , q , mp , mq , sq)) =
    let (t , l , r) = useExch sq sp
    in tapp r (subT mp l a arg) (delT mq b)
  go (inr (p , q , mp , mq , sq)) =
    let (t , l , r) = useAssoc sq sp
    in tapp r (delT mp a) (subT mq l b arg)
subT m sp (tlam b) arg =
  tlam (subT (mthere true m) (uleft sp) b (insT mhere arg))

-- THE HEADLINE. Substitution is a term of the calculus, at the
-- multiplicative connective.
substT : (BodyOf TmG ⊛ TmG) ⊢ TmG
substT = ⊛-E' (BodyOf TmG) TmG λ u u₁ u₂ s b a → subT mhere s b a

-- 3.4 ... AND SUBSTITUTION IS THE INTERNAL HOM.

-- PRIMITIVE (phase 1): the zipper view of a usage splitting.
linFocus : Focus linFib appop true
linFocus .SplitAt u₁   = Σ[ u₂ ∈ Usage ] Σ[ u ∈ Usage ] Use⊎ u₁ u₂ u
linFocus .whole  sa    = sa .snd .fst
linFocus .Rest         = Unit
linFocus .restOf _     = false
linFocus .restSlot sa _ = sa .fst

open FocusNotation linFocus

-- the arity family of a β-redex: body on the left, argument on the
-- right.  `⊸ᶠ` reads it only at `restOf tt = false`.
Redex : (a : Bool) → Ctx
Redex = boolΠ (BodyOf TmG) TmG

-- SUBSTITUTION, CURRIED.  No transport, no equation component.
substCurried : BodyOf TmG ⊢ ⊸ᶠ Redex TmG
substCurried u₁ b (u₂ , u , s) k = subT mhere s b (k tt)

-- PRIMITIVE (phase 1): the focused splittings ARE the splittings.
-- This is the bridge `Fibered.agda` leaves to the instance, and it is
-- the only thing standing between `⊸ᶠ` and `⊛`.
focusApp : {B : Ctx} → (BodyOf TmG ⊢ ⊸ᶠ Redex B) → (BodyOf TmG ⊛ TmG) ⊢ B
focusApp g = ⊛-E' (BodyOf TmG) TmG λ u u₁ u₂ s b a → g u₁ b (u₂ , u , s) (λ _ → a)

focusLam : {B : Ctx} → ((BodyOf TmG ⊛ TmG) ⊢ B) → BodyOf TmG ⊢ ⊸ᶠ Redex B
focusLam f u₁ b (u₂ , u , s) k = f u (⊛-mk (BodyOf TmG) TmG u u₁ u₂ s b (k tt))

-- THEOREM.  β IS EVALUATION AT THE RESIDUAL, definitionally.
substIsApp : substT ≡ focusApp substCurried
substIsApp = refl

-- ... and the currying is an isomorphism. ONE direction is `refl`; the
-- other costs exactly one instance of the documented trap "arities have no
-- η" -- `boolΠ (k true) (k false)` is not `k`, so rebuilding a payload
-- from its two slots is only PROPOSITIONALLY the identity.
private
  boolΠ-η : ∀ {ℓ} {M : Bool → Type ℓ} (k : (b : Bool) → M b)
          → boolΠ {M = M} (k true) (k false) ≡ k
  boolΠ-η {M = M} k =
    funExt (boolΠ {M = λ b → boolΠ {M = M} (k true) (k false) b ≡ k b} refl refl)

focusRet : {B : Ctx} (g : BodyOf TmG ⊢ ⊸ᶠ Redex B) → focusLam (focusApp g) ≡ g
focusRet g = refl

focusSec : {B : Ctx} (f : (BodyOf TmG ⊛ TmG) ⊢ B) → focusApp (focusLam f) ≡ f
focusSec f = funExt λ u → funExt λ x → cong (λ z → f u (x .fst , z)) (boolΠ-η (x .snd))

substUP : {B : Ctx} → Iso ((BodyOf TmG ⊛ TmG) ⊢ B) (BodyOf TmG ⊢ ⊸ᶠ Redex B)
substUP .Iso.fun = focusLam
substUP .Iso.inv = focusApp
substUP .Iso.sec = focusRet
substUP .Iso.ret = focusSec

-- §4  THE BUDGET, and DEAD-CODE ELIMINATION IS VACUOUS.
--
-- The motive of the fold is the statement being proved.

-- occurrences = live variables + binders `Budget` IS a connective
-- composite: two `⊕ᴰ`s over `ℕ` (both tags are plain types, independent of
-- the world) around the invariant, which is the only part that mentions
-- the world.
BudgetEqn : ℕ → ℕ → Ctx
BudgetEqn oc lm u = oc ≡ live u + lm

Budget : Ctx
Budget = ⊕ᴰ ℕ λ oc → ⊕ᴰ ℕ λ lm → BudgetEqn oc lm

private
  shuffle : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  shuffle a b c d =
      sym (+-assoc a b (c + d))
    ∙ cong (a +_) (+-assoc b c d)
    ∙ cong (λ z → a + (z + d)) (+-comm b c)
    ∙ cong (a +_) (sym (+-assoc c b d))
    ∙ +-assoc a c (b + d)

-- one variable, no binder: `soloLive` is the whole content
budgetVar : SoloG ⊢ Budget
budgetVar u s = 1 , 0 , sym (+-zero (live u) ∙ soloLive u s)

-- occurrences add, binders add, and the usages add by `liveSplit`
-- (a primitive of `Context.agda`, not a new proof)
budgetApp : (Budget ⊛ Budget) ⊢ Budget
budgetApp = ⊛-E' Budget Budget
  λ u u₁ u₂ s (o₁ , l₁ , e₁) (o₂ , l₂ , e₂) →
    (o₁ + o₂) , (l₁ + l₂) ,
      ( cong₂ _+_ e₁ e₂
      ∙ shuffle (live u₁) l₁ (live u₂) l₂
      ∙ cong (_+ (l₁ + l₂)) (liveSplit s))

-- a binder trades one live variable for one binder: the invariant is
-- literally `+-suc` Phase 1 is not the issue: the two `⊕ᴰ` tags are plain
-- numbers, so the body is arithmetic on them -- a semantic action, which
-- is allowed.
budgetLam : BodyOf Budget ⊢ Budget
budgetLam u (o , l , e) = o , suc l , (e ∙ sym (+-suc (live u) l))

budgetAlg : StepG Budget ⊢ Budget
budgetAlg = ⊕-E budgetVar (⊕-E budgetApp budgetLam)

-- THE INTRINSIC INVARIANT, as a term of the calculus.
budget : TmG ⊢ Budget
budget = foldTm Budget budgetAlg

occOf : ∀ {u} → Tm u → ℕ
occOf {u} t = budget u t .fst

lamOf : ∀ {u} → Tm u → ℕ
lamOf {u} t = budget u t .snd .fst

budgetEq : ∀ {u} (t : Tm u) → occOf t ≡ live u + lamOf t
budgetEq {u} t = budget u t .snd .snd

private
  noSucSelf : (n : ℕ) → suc n ≡ n → ⊥
  noSucSelf zero    p = snotz p
  noSucSelf (suc n) p = noSucSelf n (injSuc p)

-- A DEAD BINDER, spelled out. `b` is the body of a `λ`; `c` is what a
-- dead-code eliminator would return in its place, at the SMALLER usage
-- (the binder gone, the variable never mentioned).

DeadBinder : Ctx
DeadBinder u =
  Σ[ b ∈ BodyOf TmG u ] Σ[ c ∈ TmG u ]
    ((occOf b ≡ occOf c) × (lamOf b ≡ lamOf c))

-- THEOREM. THE DEAD-BINDER GRAMMAR IS EMPTY.
deadBinder : DeadBinder ⊢ ⊥G
deadBinder u (b , c , eo , el) = E.rec (noSucSelf (live u + lamOf b) contradiction)
  where
  -- occ b = live (true ∷ u) + lam b = suc (live u + lam b)
  contradiction : suc (live u + lamOf b) ≡ live u + lamOf b
  contradiction =
      sym (budgetEq b)
    ∙ eo
    ∙ budgetEq c
    ∙ cong (live u +_) (sym el)

-- COROLLARY. A dead-code eliminator's rewriting branch is `⊥-E`, so there
-- is nothing to choose: any two of them agree, and the pass is the
-- identity.
stripDead : DeadBinder ⊢ TmG
stripDead = ⊥-E ∘g deadBinder

dceUnique : (f g : DeadBinder ⊢ TmG) → f ≡ g
dceUnique f g = funExt λ u → funExt λ d → E.rec* (deadBinder u d)

-- ... hence the honest dead-code-elimination pass
dcePass : Pass
dcePass = idPass

-- The other half of "no variable is dropped or duplicated": a usage that
-- owns a live variable does not split as itself twice.

noSelfSplit : (u : Usage) → 0 < live u → Use⊎ u u u → ⊥
noSelfSplit []          p _         = ¬-<-zero p
noSelfSplit (true  ∷ u) p ()
noSelfSplit (false ∷ u) p (uskip s) = noSelfSplit u p s

-- §5  THE PASSES.  From here on there is no pointful Agda at all.

-- 5.1  Two views, built from `unroll` alone.

-- "is it a variable?"  The negative branch keeps the term, because
-- `roll` puts back what `unroll` took apart.
isVarView : TmG ⊢ (SoloG ⊕ TmG)
isVarView =
  ⊕-E {A = SoloG} {C = SoloG ⊕ TmG} {B = (TmG ⊛ TmG) ⊕ BodyOf TmG}
      ⊕-I₁ (⊕-I₂ ∘g (⊕-E appT lamT))
  ∘g unroll

-- "is it a λ?"  The positive branch hands back the BODY, which is
-- what β needs.
lamView : TmG ⊢ (BodyOf TmG ⊕ TmG)
lamView =
  ⊕-E {A = SoloG} {C = BodyOf TmG ⊕ TmG} {B = (TmG ⊛ TmG) ⊕ BodyOf TmG}
      (⊕-I₂ ∘g varT)
      (⊕-E (⊕-I₂ ∘g appT) ⊕-I₁)
  ∘g unroll

-- 5.2 β-CONTRACTION. One alternative of `roll` replaced. look at the
-- function part ⊛-map lamView idg push the choice out of the tensor
-- ⊛-distL it was a λ: substitute; else: rebuild ⊕-E substT appT Read the
-- middle line: `⊛-distL` is exactly the step that a cartesian calculus
-- would need `&` for.

betaApp : (TmG ⊛ TmG) ⊢ TmG
betaApp =
  ⊕-E substT appT
  ∘g ⊛-distL (BodyOf TmG) TmG TmG
  ∘g ⊛-map lamView idg

betaAlg : StepG TmG ⊢ TmG
betaAlg = ⊕-E varT (⊕-E betaApp lamT)

-- A single bottom-up sweep, NOT a normaliser: contracting a redex can
-- expose a new one at an ancestor, and this pass does not revisit it.
betaPass : Pass
betaPass = foldTm TmG betaAlg

-- 5.3 η-CONTRACTION. `λx. f x ↦ f`.

etaApp : BodyOf (TmG ⊛ TmG) ⊢ TmG
etaApp =
  ⊕-E (lamT ∘g under appT ∘g unfreshL)
      ( ⊕-E soloUnit (lamT ∘g under appT ∘g unfreshR)
        ∘g ⊛-distR TmG (BodyOf SoloG) (BodyOf TmG)
        ∘g ⊛-map idg (under isVarView))
  ∘g freshSplit

etaLam : BodyOf TmG ⊢ TmG
etaLam =
  ⊕-E (lamT ∘g under varT)
      (⊕-E etaApp (lamT ∘g under lamT))
  ∘g under unroll

etaAlg : StepG TmG ⊢ TmG
etaAlg = ⊕-E varT (⊕-E appT etaLam)

etaPass : Pass
etaPass = foldTm TmG etaAlg

-- 5.4  A PIPELINE.  `_then_` is `Syntax.agda`'s; passes are the
-- endomorphisms of `TmG` in the category of the calculus, so
-- composing them is `_∘g_` and nothing has to be checked.

optimise : Pass
optimise = betaPass then etaPass then dcePass

-- §6  IT COMPUTES.

-- `λx. x` at the empty usage, with the binder's variable live
idLin0 : Tm (false ∷ [])
idLin0 = tlam (tvar tt)

-- `(λx.x) (λx.x)`, at the usage `false ∷ []`
selfApp0 : Tm (false ∷ [])
selfApp0 = tapp (uskip unil) idLin0 idLin0

-- an η-redex whose function part is NOT a λ, so only η can fire
etaRedex : Tm []
etaRedex = tlam (tapp (uright unil) selfApp0 (tvar tt))

-- ... and one whose function part is a λ, so β fires first
betaEtaRedex : Tm []
betaEtaRedex = tlam (tapp (uright unil) idLin0 (tvar tt))

_ : idPass [] idLin ≡ idLin
_ = refl

_ : betaPass [] selfApp ≡ idLin
_ = refl

_ : etaPass [] etaRedex ≡ selfApp
_ = refl

_ : etaPass [] betaEtaRedex ≡ idLin
_ = refl

-- β then η: `(λx. (λy.y) x)` ↦ `λx. x` by β, and the η-redex is gone
_ : optimise [] betaEtaRedex ≡ idLin
_ = refl

-- the identity pass really is the fold of the typing rules, at a point
_ : foldTm TmG roll [] selfApp ≡ selfApp
_ = refl

{- ================================================================== WHAT
   THE INDEX BOUGHT -- and where it bought nothing.
   ==================================================================
   BOUGHT. * The substitution lemma. -}
