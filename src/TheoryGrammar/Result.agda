{-
  THE EXCEPTION MONAD, generic in the theory.

  Every "shape of parser" written anywhere in this development is the
  SAME connective at a different error grammar:

      Result E A  =  A ⊕ E

      ⊤ ⊢ Result ⊥G     A     a total map -- cannot fail
      ⊤ ⊢ Result ⊤G     A     an incomplete parser -- fails, says nothing
      ⊤ ⊢ Result (¬G A) A     a DECISION -- fails WITH a refutation
      ⊤ ⊢ Result A'     A     a `Decision A A'`, once `(A & A') ⊢ ⊥`

  The last two are not new definitions: `Dec⟨ A ⟩` IS `Result (¬G A) A`
  definitionally (checked below), and `Decidable.Additive.Decision`'s
  `decide` field IS a `⊤G ⊢ Result A' A`.  So the shapes were already
  the same thing and only the spelling differed.

  What that buys, and the reason this file exists:

      mapE ⊤-I : Result E A ⊢ MaybeG A

  is a SINGLE map that levels every shape to a common one, uniformly in
  `E`, with no per-shape code.  Running a parser, chaining two of them,
  or observing one in a test case is therefore written once here rather
  than once per instance -- which is what `Strings.Examples.succeeded`,
  `Strings.Examples.isYes`, `Lambda.Tests.closed!`,
  `SimplyTyped.Tests.infers!` and `Modes.Core.accepts` all were.

  Additive throughout: nothing here mentions the operations, so a
  `Model` suffices, exactly as in `Decidable.Additive`.  Every proof is
  a composite of `Rules`' intro/elim -- no `⊎`, no `Maybe`, and not one
  case split on a sum.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Result where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Rules
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Distributive

private variable ℓS ℓ ℓ' ℓX ℓA ℓB ℓC ℓD ℓE ℓE' ℓY ℓZ : Level


module Res {S : Type ℓS} (Car : S → Type ℓX) where

  open CarrierNotation Car
  open RulesCarrier Car
  open DecAdd Car using (¬G_; Dec⟨_⟩; &-swap; contra; Complement; Decision; ⊕-E-at; ⊕-E-atᴰ)
  open Dist Car using (dist&r)

  private variable
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s
    D : TheoryTy ℓD s
    E : TheoryTy ℓE s
    E' : TheoryTy ℓE' s

  -- ================================================================
  -- The shape.  `E` is the error grammar: what a failure CARRIES.
  -- ================================================================

  Result : TheoryTy ℓE s → TheoryTy ℓA s → TheoryTy (ℓ-max ℓA ℓE) s
  Result E A = A ⊕ E

  -- The intro rules, with BOTH grammars named.  Naming them is not
  -- optional: `Result E A` unfolds to `A m ⊎ E m`, and a grammar-valued
  -- implicit cannot be recovered from that.
  ok : (E : TheoryTy ℓE s) (A : TheoryTy ℓA s) → A ⊢ Result E A
  ok E A = ⊕-I₁ {A = A} {B = E}

  err : (E : TheoryTy ℓE s) (A : TheoryTy ℓA s) → E ⊢ Result E A
  err E A = ⊕-I₂ {B = E} {A = A}

  -- elim is `⊕-E`; named so the shape is visible at the use site
  caseR : {E : TheoryTy ℓE s} {A : TheoryTy ℓA s} {C : TheoryTy ℓC s}
        → A ⊢ C → E ⊢ C → Result E A ⊢ C
  caseR = ⊕-E

  -- ... and the POINTWISE elimination, for exactly the reason
  -- `Decidable.Additive.dec-elim` exists: a branch may need data that
  -- lives at ONE world -- a recursive call at THIS subterm, a
  -- certificate about THIS part -- and `caseR`'s branches quantify over
  -- the index.  `Result E A` is `A ⊕ E`, so this is `⊕-E-at` renamed;
  -- nothing new is assumed, only the quantifier is moved.  Instances
  -- call it and never match `inl`/`inr` themselves.
  caseR-at : (E : TheoryTy ℓE s) (A : TheoryTy ℓA s) (m : Car s)
             {Z : Type ℓZ}
           → (A m → Z) → (E m → Z) → Result E A m → Z
  caseR-at E A m = ⊕-E-at A E m

  -- ================================================================
  -- The monad, in the success variable.
  -- ================================================================

  bindR : (E : TheoryTy ℓE s) (B : TheoryTy ℓB s) {A : TheoryTy ℓA s}
        → A ⊢ Result E B → Result E A ⊢ Result E B
  bindR E B f = caseR f (err E B)

  mapR : (E : TheoryTy ℓE s) (B : TheoryTy ℓB s) {A : TheoryTy ℓA s}
       → A ⊢ B → Result E A ⊢ Result E B
  mapR E B f = bindR E B (ok E B ∘⊢ f)

  joinR : (E : TheoryTy ℓE s) (A : TheoryTy ℓA s)
        → Result E (Result E A) ⊢ Result E A
  joinR E A = caseR id⊢ (err E A)

  -- ... and contravariantly in the error, which is where the uniform
  -- interface below comes from
  mapE : (E' : TheoryTy ℓE' s) (A : TheoryTy ℓA s) {E : TheoryTy ℓE s}
       → E ⊢ E' → Result E A ⊢ Result E' A
  mapE E' A g = caseR (ok E' A) (err E' A ∘⊢ g)

  catchR : (E' : TheoryTy ℓE' s) (A : TheoryTy ℓA s) {E : TheoryTy ℓE s}
         → E ⊢ Result E' A → Result E A ⊢ Result E' A
  catchR E' A h = caseR (ok E' A) h

  -- ================================================================
  -- ALTERNATION.  Trying a second parser after the first fails needs to
  -- say what happens to the FIRST failure -- that is the whole content,
  -- and it is one hypothesis `(E & E) ⊢ E`.  At `E = ⊤G` it is `&-E₁`
  -- and nothing is carried; at `E = ¬G A` it is also `&-E₁`, and the
  -- refutation of the first alternative is discarded, which is why
  -- deciding an alternation needs `dec-⊕`, not this.
  --
  -- `⊕-E` into an internal hom, so the first alternative is eliminated
  -- by the rule rather than matched.
  -- ================================================================

  module _ (E : TheoryTy ℓE s) (A : TheoryTy ℓA s) (j : (E & E) ⊢ E) where

    orElseR : Result E A ⊢ (Result E A ⇒ Result E A)
    orElseR =
      caseR (⇒-I (ok E A ∘⊢ &-E₁))
            (⇒-I (caseR (ok E A ∘⊢ &-E₂) (err E A ∘⊢ j) ∘⊢ dist&r))

    altR : {X : TheoryTy ℓB s} → X ⊢ Result E A → X ⊢ Result E A
         → X ⊢ Result E A
    altR f g = ⇒-E (orElseR ∘⊢ f) g

    -- Search over a finite space of alternatives.  The `List` is the
    -- search SPACE -- a parameter of the algorithm, like `allRules` --
    -- not a value being computed with; `X ⊢ E` is what to do when it
    -- runs out.
    altList : {X : TheoryTy ℓB s} → X ⊢ E → (Y : Type ℓY) → List Y
            → (Y → X ⊢ Result E A) → X ⊢ Result E A
    altList k Y []       f = err E A ∘⊢ k
    altList k Y (y ∷ ys) f = altR (f y) (altList k Y ys f)

  -- ================================================================
  -- THE INDEXED SUM, SEARCHED.  The parser's counterpart of
  -- `Decidable.Listable.dec-⊕ᴰ`, and strictly weaker: `dec-⊕ᴰ` needs
  -- the list COMPLETE, because refuting `⊕ᴰ Y A` means refuting every
  -- tag.  Here failure carries `E` and claims nothing, so the list is a
  -- search SPACE and completeness never appears.
  --
  -- A composite of `altList`, `mapR` and `&ᴰ-E`: no `⊎`, no recursion
  -- of its own.
  -- ================================================================

  altList-⊕ᴰ : (E : TheoryTy ℓE s) (j : (E & E) ⊢ E)
               (Y : Type ℓY) (A : Y → TheoryTy ℓA s)
             → (&ᴰ Y (λ y → Result E (A y)) ⊢ E) → List Y
             → &ᴰ Y (λ y → Result E (A y)) ⊢ Result E (⊕ᴰ Y A)
  altList-⊕ᴰ E j Y A k ys =
    altList E (⊕ᴰ Y A) j k Y ys
      λ y → mapR E (⊕ᴰ Y A) (⊕ᴰ-I Y {A = A} y) ∘⊢ &ᴰ-E Y y

  -- ================================================================
  -- SEQUENCING, additively.  Two parsers at the same world, and both
  -- must succeed.  (The MULTIPLICATIVE sequencing -- one parser per
  -- slot of an operation -- is `Result.Fib` below, since it needs a
  -- promodel.)
  -- ================================================================

  bothR : (E : TheoryTy ℓE s) (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
          {X : TheoryTy ℓC s}
        → X ⊢ Result E A → X ⊢ Result E B → X ⊢ Result E (A & B)
    -- eliminate the first result under a `⇒`, then apply to the second
  bothR E A B f g =
    ⇒-E (caseR (⇒-I (caseR (ok E (A & B)) (err E (A & B) ∘⊢ &-E₂)
                     ∘⊢ dist&r))
               (⇒-I (err E (A & B) ∘⊢ &-E₁))
         ∘⊢ f)
        g

  -- ================================================================
  -- THE SHAPES.  Each is `Result` at a particular error grammar; none
  -- of them is a new definition.
  -- ================================================================

  -- (1) failure carrying nothing.  This is the option type, and it now
  -- has the monad above rather than a `with`.
  MaybeG : TheoryTy ℓA s → TheoryTy ℓA s
  MaybeG {s = s} A = Result (⊤G {s}) A

  just-I : {A : TheoryTy ℓA s} → A ⊢ MaybeG A
  just-I {A = A} = ok ⊤G A

  nothing-I : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} → B ⊢ MaybeG A
  nothing-I {A = A} = err ⊤G A ∘⊢ ⊤-I

  -- elim, point-free: put the scrutinee in the context with `&-I`,
  -- distribute, and eliminate.  (This is `View.viewCase` at a Maybe.)
  MaybeG-E : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
           → A ⊢ C → B ⊢ C → B ⊢ MaybeG A → B ⊢ C
  MaybeG-E f g h = caseR (f ∘⊢ &-E₂) (g ∘⊢ &-E₁) ∘⊢ (dist&r ∘⊢ &-I id⊢ h)

  -- errors at `⊤G` combine trivially, so alternation needs no argument
  orElseM : (A : TheoryTy ℓA s) → MaybeG A ⊢ (MaybeG A ⇒ MaybeG A)
  orElseM A = orElseR ⊤G A &-E₁

  altM : (A : TheoryTy ℓA s) {X : TheoryTy ℓB s}
       → X ⊢ MaybeG A → X ⊢ MaybeG A → X ⊢ MaybeG A
  altM A = altR ⊤G A &-E₁

  altListM : (A : TheoryTy ℓA s) {X : TheoryTy ℓB s} (Y : Type ℓY)
           → List Y → (Y → X ⊢ MaybeG A) → X ⊢ MaybeG A
  altListM A Y ys f = altList ⊤G A &-E₁ ⊤-I Y ys f

  -- the option-typed indexed sum: a parse for SOME rule.  `dec-⊕ᴰ`
  -- with the completeness hypothesis deleted, which is exactly what a
  -- parser may delete.
  maybe-⊕ᴰ : (Y : Type ℓY) (A : Y → TheoryTy ℓA s) → List Y
           → &ᴰ Y (λ y → MaybeG (A y)) ⊢ MaybeG (⊕ᴰ Y A)
  maybe-⊕ᴰ Y A = altList-⊕ᴰ ⊤G &-E₁ Y A ⊤-I

  -- (2) failure carrying a refutation.  NOT a new definition:
  private
    _ : {A : TheoryTy ℓA s} → Dec⟨ A ⟩ ≡ Result (¬G A) A
    _ = refl

  -- (3) failure impossible
  runCover : (A : TheoryTy ℓA s) → Result (⊥G {s}) A ⊢ A
  runCover A = caseR id⊢ ⊥-E

  -- ================================================================
  -- THE UNIFORM INTERFACE.  One map, uniform in `E`, that takes EVERY
  -- shape above to the same one.  A test harness, a chaining
  -- combinator, or a pretty-printer written against `MaybeG` therefore
  -- applies to all of them without a per-shape case.
  -- ================================================================

  toMaybe : (A : TheoryTy ℓA s) {E : TheoryTy ℓE s} → Result E A ⊢ MaybeG A
  toMaybe A = mapE ⊤G A ⊤-I

  -- A `Decision A A'` (Decidable.Additive) is exactly a cover of a
  -- `Result A' A` plus the exclusion; recorded so the two vocabularies
  -- are visibly the same one.
  private
    _ : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
      → Decision A A' → ⊤G ⊢ Result A' A
    _ = Decision.decide

    _ : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
      → Decision A A' → (A & A') ⊢ ⊥G
    _ = Decision.exclude
