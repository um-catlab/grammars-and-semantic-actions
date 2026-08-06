{-
  SEMANTIC ACTIONS, and the one way out of the calculus.

  `Δ X = ⊕ᴰ X (λ _ → ⊤G)` is the DISCRETE type on a metalanguage type
  `X`: a value of `Δ X` at a world is an `x : X` and nothing else.  A
  semantic action is a term into one,

      Action A X  =  A ⊢ Δ X

  and that is the whole notion -- ported from `Grammar.SemanticAction`,
  which is stated for strings, by re-indexing and nothing else.

  What `Δ` is FOR is the externalisation:

      run : (⊤G ⊢ Δ X) → (m : carrier s) → X

  A cover of `Δ X` is a family of `X`s over the worlds, so `run` is the
  only place a term leaves the calculus, and every observation of a
  program -- a test case, a pretty-print, a benchmark -- factors as

      ⊤G ⊢ P     the program        (Views.Cover P)
      P  ⊢ Δ X   the action         what to observe
      run        the externalisation

  Because `Result` (TheoryGrammar.Result) unified the SHAPES of `P`, the
  observations below are written once for all of them: `accepts?` and
  `runResult` apply verbatim to an incomplete parser, a decision, a
  `Decision A A'`, and a total map.  This is what
  `Strings.Examples.succeeded`/`isYes`, `Lambda.Tests.closed!`/`some`/
  `none`, `SimplyTyped.Tests.infers!`/`checks!`/`synth` and
  `Passes.Tests.runClosed` each were, separately.

  Levels: `Δ` lands at the level of `X` alone (`⊤G` is at `ℓ-zero`), so
  observing at `Bool` costs nothing.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.SemanticAction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; map)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Inductive
open import TheoryGrammar.Distributive
open import TheoryGrammar.Result

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓE ℓY ℓZ ℓW : Level


-- ==================================================================
-- §0  TEST SUITES.  Independent of any theory: once `run` has produced
--     a metalanguage value, checking a batch of cases is list algebra.
--
--     A CASE is `observed ↦ expected`, a SUITE is a list of them, and
--
--         passes cs  =  map fst cs ≡ map snd cs
--
--     is the statement that every case holds -- proved by ONE `refl`
--     exactly when every case holds definitionally.  Writing a suite
--     rather than N separate `_ : … ≡ …` declarations also keeps the
--     term under test written once.
-- ==================================================================

module Suite where

  Case : Type ℓY → Type ℓY
  Case X = X × X

  -- `input ↦ expected`.  Heterogeneous, because with `_at_` below the
  -- left component is the WORLD to run at and the right is the value.
  infix 6 _↦_
  _↦_ : {W : Type ℓZ} {X : Type ℓY} → W → X → W × X
  a ↦ b = a , b

  -- ... and the whole suite as one proposition
  passes : {X : Type ℓY} → List (Case X) → Type ℓY
  passes cs = map fst cs ≡ map snd cs

  -- The common shape: ONE observation applied at many worlds.  Written
  -- `p at (w₁ ↦ v₁ ∷ … ∷ [])`, so the term under test appears once.
  infix 3 _at_
  _at_ : {W : Type ℓZ} {X : Type ℓY}
       → (W → X) → List (W × X) → List (Case X)
  f at cs = map (λ c → f (c .fst) ↦ c .snd) cs

open Suite public


-- ==================================================================
-- §1  ADDITIVELY.  Nothing here mentions the operations, so a `Model`
--     suffices -- exactly as in `Decidable.Additive` and `Result`.
-- ==================================================================

module Act {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Car : S → Type ℓX) where

  open CarrierNotation Car
  open RulesCarrier Car
  open Dist Car using (⊕ᴰ-&-in)
  open Res Car using (Result; ok; err; caseR; MaybeG; toMaybe)

  private variable
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s
    E : TheoryTy ℓE s

  -- ================================================================
  -- The discrete type, and actions into it.
  -- ================================================================

  Δ : {s : S} → Type ℓY → TheoryTy ℓY s
  Δ X = ⊕ᴰ X (λ _ → ⊤G)

  Action : TheoryTy ℓA s → Type ℓY → Type (ℓ-max ℓX (ℓ-max ℓA ℓY))
  Action A X = A ⊢ Δ X

  -- intro: a constant observation
  pureA : {A : TheoryTy ℓA s} (X : Type ℓY) (x : X) → Action A X
  pureA X x = ⊕ᴰ-I X {A = λ _ → ⊤G} x ∘⊢ ⊤-I

  -- elim: `Δ X` is a `⊕ᴰ`, so its rule is `⊕ᴰ-E`
  Δ-E : {X : Type ℓY} {B : TheoryTy ℓB s} → (X → ⊤G {s} ⊢ B) → Δ X ⊢ B
  Δ-E f = ⊕ᴰ-E f

  Δ-map : {X : Type ℓY} {Z : Type ℓZ} → (X → Z) → Δ {s = s} X ⊢ Δ {s = s} Z
  Δ-map {Z = Z} f = Δ-E λ x → pureA Z (f x)

  -- the identity action: `Δ X` observes itself
  idA : {X : Type ℓY} → Action (Δ {s = s} X) X
  idA = id⊢

  -- PRIMITIVE, and the DEFINING property: `Δ X` does not depend on the
  -- world, so its elements move between worlds for free.  That is
  -- exactly what makes `Δ` the externalisation, and it is what lets an
  -- action combine payloads sitting at DIFFERENT worlds -- the slots of
  -- a splitting -- with no residual.  `Δ-⊗` (§2) is the point-free
  -- form; this is the form needed wherever the slot family is an
  -- extended lambda and so cannot be unified against (arities have no
  -- η) -- see `Lambda.DeBruijn`.
  Δ-at : {X : Type ℓY} (m m' : Car s) → Δ {s = s} X m → Δ {s = s} X m'
  Δ-at m m' d = d

  -- ================================================================
  -- Functoriality, in both variables.  These are the only two ways to
  -- build an action from another one, and both are `_∘⊢_`.
  -- ================================================================

  mapA : {A : TheoryTy ℓA s} {X : Type ℓY} {Z : Type ℓZ}
       → (X → Z) → Action A X → Action A Z
  mapA f a = Δ-map f ∘⊢ a

  -- reindex along a term: this is why an action composes with a parser
  preA : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓY}
       → A ⊢ B → Action B X → Action A X
  preA f a = a ∘⊢ f

  -- ================================================================
  -- One action per connective.
  -- ================================================================

  -- `&`, both projections and the pairing
  &A₁ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓY}
      → Action A X → Action (A & B) X
  &A₁ a = a ∘⊢ &-E₁

  &A₂ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓY}
      → Action B X → Action (A & B) X
  &A₂ b = b ∘⊢ &-E₂

  -- `Δ` takes `&` to `×`.  The index has to be pulled out of the
  -- conjunct, which is `Dist.⊕ᴰ-&-in` -- no case split.
  Δ-pair : {X : Type ℓY} {Z : Type ℓZ} → (Δ {s = s} X & Δ {s = s} Z) ⊢ Δ {s = s} (X × Z)
  Δ-pair {X = X} {Z = Z} =
    ⊕ᴰ-E (λ z → Δ-map (λ x → (x , z)) ∘⊢ &-E₁)
    ∘⊢ ⊕ᴰ-&-in Z {A = Δ X} {P = λ _ → ⊤G}

  pairA : {A : TheoryTy ℓA s} {X : Type ℓY} {Z : Type ℓZ}
        → Action A X → Action A Z → Action A (X × Z)
  pairA a b = Δ-pair ∘⊢ &-I a b

  -- `⊕`, tagged and untagged
  caseA : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓY}
        → Action A X → Action B X → Action (A ⊕ B) X
  caseA = ⊕-E

  ⊕A : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {X : Type ℓY} {Z : Type ℓZ}
     → Action A X → Action B Z → Action (A ⊕ B) (X ⊎ Z)
  ⊕A a b = caseA (mapA inl a) (mapA inr b)

  -- `⊕ᴰ`: the index is observable, with or without the payload
  ⊕ᴰA : {Y : Type ℓY} {A : Y → TheoryTy ℓA s} {Z : Y → Type ℓZ}
      → ((y : Y) → Action (A y) (Z y)) → Action (⊕ᴰ Y A) (Σ Y Z)
  ⊕ᴰA {Y = Y} {Z = Z} f = ⊕ᴰ-E λ y → mapA (y ,_) (f y)

  tagA : (Y : Type ℓY) {A : Y → TheoryTy ℓA s} → Action (⊕ᴰ Y A) Y
  tagA Y = ⊕ᴰ-E λ y → pureA Y y

  -- `&ᴰ`: observe at one index
  &ᴰA : (Y : Type ℓY) {A : Y → TheoryTy ℓA s} {X : Type ℓZ} (y : Y)
      → Action (A y) X → Action (&ᴰ Y A) X
  &ᴰA Y y a = a ∘⊢ &ᴰ-E Y y

  -- `⊥` observes anything
  ⊥A : {X : Type ℓY} → Action (⊥G {s}) X
  ⊥A = ⊥-E

  -- a representable is observed by naming what to say there
  ⌈⌉A : {a : Car s} {X : Type ℓY} → X → Action ⌈ a ⌉ X
  ⌈⌉A {X = X} x = pureA X x

  -- ================================================================
  -- EXTERNALISATION.  The only place a term leaves the calculus.
  -- ================================================================

  run : {s : S} {X : Type ℓY} → ⊤G {s} ⊢ Δ {s = s} X → Car s → X
  run f m = f m tt .fst

  -- a program (`Views.Cover P`) observed by an action
  observe : {P : TheoryTy ℓA s} {X : Type ℓY}
          → ⊤G ⊢ P → Action P X → Car s → X
  observe p a = run (a ∘⊢ p)

  -- ================================================================
  -- OBSERVING A RESULT.  Uniform in the error grammar, so ONE
  -- definition covers `MaybeG A`, `Dec⟨ A ⟩`, a `Decision A A'`, and a
  -- total map -- see `TheoryGrammar.Result`.
  -- ================================================================

  -- did it succeed?  This is every `succeeded`/`isYes`/`closed!`/
  -- `infers!`/`accepts` in the instances, at once.
  okA : (A : TheoryTy ℓA s) (E : TheoryTy ℓE s) → Action (Result E A) Bool
  okA A E = caseA (pureA Bool true) (pureA Bool false)

  accepts? : (A : TheoryTy ℓA s) (E : TheoryTy ℓE s)
           → ⊤G ⊢ Result E A → Car s → Bool
  accepts? A E p = observe p (okA A E)

  -- what did it produce?  The failure is observed too, at `Unit`, so
  -- this is `⊕A` followed by the evident renaming.
  maybeA : (A : TheoryTy ℓA s) (E : TheoryTy ℓE s) {X : Type ℓY}
         → Action A X → Action (Result E A) (Maybe X)
  maybeA A E {X = X} a = caseA (mapA just a) (pureA (Maybe X) nothing)

  runResult : (A : TheoryTy ℓA s) (E : TheoryTy ℓE s) {X : Type ℓY}
            → ⊤G ⊢ Result E A → Action A X → Car s → Maybe X
  runResult A E p a = observe p (maybeA A E a)

  -- ... and the form that keeps the action INSIDE the term.  A program
  -- whose semantic action has already been applied is
  --
  --     mapR E (Δ X) act ∘⊢ p   :   ⊤G ⊢ Result E (Δ X)
  --
  -- which is still a term of the calculus -- the witness sits in `Δ`,
  -- the failure still carries whatever `E` carries, and nothing has been
  -- externalised.  `runΔ` is then the SINGLE place it leaves, and it
  -- belongs at the OBSERVATION, not at the definition of the pipeline:
  -- a name like `elab : Raw → Maybe (DB 0)` has already left.
  runΔ : (X : Type ℓY) (E : TheoryTy ℓE s)
       → ⊤G ⊢ Result E (Δ {s = s} X) → Car s → Maybe X
  runΔ X E p = runResult (Δ X) E p idA

  -- ... and with the failure observed as well
  eitherA : (A : TheoryTy ℓA s) (E : TheoryTy ℓE s)
            {X : Type ℓY} {Z : Type ℓZ}
          → Action A X → Action E Z → Action (Result E A) (X ⊎ Z)
  eitherA A E a b = ⊕A a b

  runEither : (A : TheoryTy ℓA s) (E : TheoryTy ℓE s)
              {X : Type ℓY} {Z : Type ℓZ}
            → ⊤G ⊢ Result E A → Action A X → Action E Z
            → Car s → X ⊎ Z
  runEither A E p a b = observe p (eitherA A E a b)


-- ==================================================================
-- §2  MULTIPLICATIVELY.  One primitive -- `Δ` absorbs a tensor -- and
--     the slotwise action is its composite with the tensor's own map.
-- ==================================================================

module ActFib {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (Fib : Fibered σ ℓX ℓP) where

  open RulesF Fib
  open Act {σ = σ} (Fib .carrier) public

  -- PRIMITIVE.  A splitting with a discrete payload at every slot is a
  -- discrete payload at the whole: the splitting itself is discarded,
  -- which is exactly what "semantic action" means.  Every other
  -- multiplicative action factors through this one.
  Δ-⊗ : (o : σ .ops) (X : (a : σ .arities o) → Type ℓY)
      → ⊗ˢ o (λ a → Δ (X a)) ⊢ Δ ((a : σ .arities o) → X a)
  Δ-⊗ o X m (sp , h) = (λ a → h a .fst) , tt

  ⊗A : (o : σ .ops)
       {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
       (X : (a : σ .arities o) → Type ℓY)
     → ((a : σ .arities o) → Action (A a) (X a))
     → Action (⊗ˢ o A) ((a : σ .arities o) → X a)
  ⊗A o {A = A} X f = Δ-⊗ o X ∘g ⊗ˢ-map o {A = A} {B = λ a → Δ (X a)} f


-- ==================================================================
-- §3  INDUCTIVELY.  A semantic action out of a generic `μ` is a
--     `Δ`-valued algebra, and the recursion is `Inductive.foldC`.  This
--     is `Grammar.SemanticAction.semact-rec`, re-indexed.
-- ==================================================================

module ActInd {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (Fib : Fibered σ ℓX ℓP) (ℓA : Level)
              (V : Type ℓY) (vs : V → S) where

  open FibNotation Fib using (TheoryTy)
  open Ind Fib ℓA V vs
  open Act {σ = σ} (Fib .carrier) using (Δ; Action)

  -- the inductive grammar at a nonterminal, as a type of the calculus
  Deriv : ((x : V) → Functor (vs x)) → (x : V) → TheoryTy ℓμ (vs x)
  Deriv F x m = μ F (x , m)

  -- ONE ACTION PER CONSTRUCTOR, which is what a `Δ`-valued algebra is.
  -- The description's `⊕e` is `⊕ᴰ` and its `⊗e` is `⊗ˢ`, so the branches
  -- are written with `⊕ᴰA` / `⊗A` above and nothing else.
  ActAlg : ((x : V) → Functor (vs x)) → (V → Type ℓSh) → Type _
  ActAlg F Z = AlgC F (λ i → Δ (Z (i .fst)) (i .snd))

  recA : {F : (x : V) → Functor (vs x)} {Z : V → Type ℓSh}
       → ActAlg F Z → (x : V) → Action (Deriv F x) (Z x)
  recA {Z = Z} α x m = foldC (λ i → Δ (Z (i .fst)) (i .snd)) α (x , m)
