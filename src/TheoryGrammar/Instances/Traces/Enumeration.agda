{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  The shuffles of `w` are finitely many, enumerated and proved complete.

  `splitProp` is FALSE here, as it is for bags -- a word splits in many
  ways -- so `DecReadable` is unavailable and `fromEnumerable` is the
  route.  Two side hypotheses, both about the independence relation and
  neither about the calculus: it must be DECIDABLE (to know which
  `right` steps exist) and PROP-VALUED (so that the enumerated proof of
  a `right` step is THE proof, and completeness can name it).
-}
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Traces.Enumeration
  (Letter : Type₀) (Ind : Letter → Letter → Type₀)
  (decInd    : (x y : Letter) → Ind x y ⊎ No (Ind x y))
  (isPropInd : (x y : Letter) → isProp (Ind x y))
  where

open import Cubical.Foundations.HLevels using (isProp×)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable

open import TheoryGrammar.Instances.Traces.Base Letter Ind public

-- ==================================================================
-- The side condition, decided and shown to be a proposition.
-- ==================================================================

decAll : (u : Word) (x : Letter) → IndepAll Ind u x ⊎ No (IndepAll Ind u x)
decAll []      x = inl tt
decAll (y ∷ u) x = cons? (decInd y x) (decAll u x)
  where
    cons? : Ind y x ⊎ No (Ind y x)
          → IndepAll Ind u x ⊎ No (IndepAll Ind u x)
          → IndepAll Ind (y ∷ u) x ⊎ No (IndepAll Ind (y ∷ u) x)
    cons? (inr k) _       = inr λ p → k (p .fst)
    cons? (inl a) (inr k) = inr λ p → k (p .snd)
    cons? (inl a) (inl b) = inl (a , b)

isPropAll : (u : Word) (x : Letter) → isProp (IndepAll Ind u x)
isPropAll []      x = isPropUnit
isPropAll (y ∷ u) x = isProp× (isPropInd y x) (isPropAll u x)

-- ==================================================================
-- The enumeration.  A shuffle of `x ∷ w` either gives `x` to the left
-- factor (always available) or to the right factor (available exactly
-- when `x` is independent of everything the left factor still owes).
-- ==================================================================

TrSp : Word → Type₀
TrSp w = Σ[ u ∈ Word ] Σ[ v ∈ Word ] ITr Ind u v w

leftsOf : {w : Word} (x : Letter) → List (TrSp w) → List (TrSp (x ∷ w))
leftsOf x = map (λ { (u , v , s) → x ∷ u , v , left s })

-- top level, not a `where`: the completeness proof has to case on the
-- same decision, and only a named function unfolds for it
pick : {w : Word} (x : Letter) (u v : Word) (s : ITr Ind u v w)
     → IndepAll Ind u x ⊎ No (IndepAll Ind u x) → List (TrSp (x ∷ w))
pick x u v s (inl pf) = (u , x ∷ v , right pf s) ∷ []
pick x u v s (inr _)  = []

rightOne : {w : Word} (x : Letter) → TrSp w → List (TrSp (x ∷ w))
rightOne x (u , v , s) = pick x u v s (decAll u x)

rightsOf : {w : Word} (x : Letter) → List (TrSp w) → List (TrSp (x ∷ w))
rightsOf x []       = []
rightsOf x (e ∷ es) = rightOne x e ++ rightsOf x es

shuffles : (w : Word) → List (TrSp w)
shuffles []      = ([] , [] , nil) ∷ []
shuffles (x ∷ w) = leftsOf x (shuffles w) ++ rightsOf x (shuffles w)

-- ==================================================================
-- Completeness.
-- ==================================================================

∈L-++ˡ : {X : Type₀} {a : X} {xs ys : List X} → a ∈L xs → a ∈L (xs ++ ys)
∈L-++ˡ here      = here
∈L-++ˡ (there p) = there (∈L-++ˡ p)

∈L-++ʳ : {X : Type₀} {a : X} (xs : List X) {ys : List X}
       → a ∈L ys → a ∈L (xs ++ ys)
∈L-++ʳ []       p = p
∈L-++ʳ (x ∷ xs) p = there (∈L-++ʳ xs p)

-- The one place a Path is transported: the enumeration stores the proof
-- the DECISION produced, and completeness is handed an arbitrary one.
-- `isPropAll` identifies them.  Nothing downstream reduces through this
-- -- it lives entirely on the refutation side of `dec-⊗-enum`.
pickIn : {w : Word} (x : Letter) (u v : Word) (s : ITr Ind u v w)
         (d : IndepAll Ind u x ⊎ No (IndepAll Ind u x)) (pf : IndepAll Ind u x)
       → (u , x ∷ v , right pf s) ∈L pick x u v s d
pickIn x u v s (inl pf') pf =
  subst (λ q → (u , x ∷ v , right q s) ∈L ((u , x ∷ v , right pf' s) ∷ []))
        (isPropAll u x pf' pf) here
pickIn x u v s (inr k)   pf = E.rec* (k pf)

rightsIn : {w : Word} (x : Letter) {u v : Word} {s : ITr Ind u v w}
           (es : List (TrSp w)) → (u , v , s) ∈L es → (pf : IndepAll Ind u x)
         → (u , x ∷ v , right pf s) ∈L rightsOf x es
rightsIn x {u} {v} {s} (_ ∷ es) here      pf =
  ∈L-++ˡ (pickIn x u v s (decAll u x) pf)
rightsIn x           (e ∷ es) (there p) pf =
  ∈L-++ʳ (rightOne x e) (rightsIn x es p pf)

complete : {u v w : Word} (s : ITr Ind u v w) → (u , v , s) ∈L shuffles w
complete nil = here
complete (left {x} s) =
  ∈L-++ˡ (∈map (λ { (u , v , t) → x ∷ u , v , left t }) (complete s))
complete (right {x} {w = w} pf s) =
  ∈L-++ʳ (leftsOf x (shuffles w)) (rightsIn x (shuffles w) (complete s) pf)

-- ==================================================================
-- In the shape `DecEnumerable` asks for.
-- ==================================================================

enumSplit : (o : MonOp) (m : Word) → List (MonSplit o m)
enumSplit nilop []      = tt ∷ []
enumSplit nilop (_ ∷ _) = []
enumSplit appop w       = shuffles w

enumComplete : (o : MonOp) (m : Word) (sp : MonSplit o m) → sp ∈L enumSplit o m
enumComplete nilop []      tt        = here
enumComplete appop w (u , v , s) = complete s
