{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CASCADE: WHAT IT MEANS FOR ONE IR TO PROJECT DOWN TO AN EARLIER
  ONE, AND WHY THE PRETTY PRINTER *IS* THAT PROJECTION.

  `Chain.Pipeline` runs six stages forward and, at exactly one place,
  backward: `sourceOf ∘ spanOf` reads a stage-3 node's retained span as
  a substring of the stage-0 input.  That is one hand-built arrow.  This
  file says what the arrow IS, so that there is one at every stage and
  they compose.

  ------------------------------------------------------------------
  A STAGE IS AN IR TOGETHER WITH WHAT IT SAYS.

      record Stage where  Ir : Type₀ ;  says : Ir → String

  `says` is the pretty printer.  It is not decoration: it is the only
  thing two objects at different stages can be compared BY, because they
  do not inhabit a common type.

  ------------------------------------------------------------------
  A PROJECTION IS A BACKWARD MAP THAT SAYS THE SAME THING.

      record B ↘ A where
        bwd   : B .Ir → A .Ir
        faith : (b : B .Ir) → A .says (bwd b) ≡ B .says b

  `faith` is the whole content, and it is what makes the projection
  worth having rather than merely typed: whatever `bwd` throws away --
  spans, usages, scoping certificates -- it does not change the program.

  THE POINT OF THE DEFINITION IS THAT `↘` COMPOSES (`_∘↘_`, `idProj`),
  so stages form a category and `bwd` from ANY stage to ANY earlier one
  is a composite that is built, not written.  That is the cascade.

  AND THE POINT OF THE *ORGANISATION* IS THAT `faith` IS FREE.  Define
  each stage's `says` as the next-lower stage's `says` after `bwd` --
  which is what a pretty printer for an IR naturally is, "turn it back
  into the thing it came from and print that" -- and every `faith` in
  the chain is `refl`.  `Chain.Unparse` does exactly this and pays
  nothing.

  ------------------------------------------------------------------
  THE FORWARD DIRECTION, AND THE TWO LAWS -- ONLY ONE OF WHICH IS TRUE
  OF THIS CHAIN.

  A pass is `A ↗ B`, i.e. `fwd : A .Ir → Maybe (B .Ir)`; the `Maybe` is
  the stage's error grammar, externalised.  Two laws relate it to a
  projection back, and the difference between them is the entire subject
  of `Chain.PrintTests`:

      Section  f p  =  ∀ b       → fwd (bwd b) ≡ just b
      Reflects f p  =  ∀ a b     → fwd a ≡ just b → fwd (bwd b) ≡ just b

  `Section` says `bwd` is a genuine section: print any object, re-run the
  pass, get that object back.  `Reflects` restricts the claim to objects
  the pass ITSELF produced -- `fwd ∘ bwd ∘ fwd ≡ fwd`, a generalised
  inverse.  It is strictly weaker and it is the honest one whenever the
  surface syntax is AMBIGUOUS, because then `bwd` cannot be injective:
  two parse trees with one token string are two objects with one
  printed form, and at most one of them survives a reparse.

  `Section` composes (`sectionComp`); `Reflects` does not, and the
  reason is exactly the failure of injectivity -- `bwd` of a later stage
  need not land in the image of the earlier pass.  So the chain gets its
  end-to-end statement from `↘`'s composition, which is unconditional,
  and its per-link forward statements one at a time.

  Nothing in this file mentions a theory, a grammar or a splitting: a
  `Stage` is data about an externalised IR, and the calculus-internal
  printers (`A ⊢ Δ String`) live in `Chain.Print`, which is where they
  belong -- `says` is what you get after `run`.
-}
open import Cubical.Foundations.Prelude

module Chain.Project where

open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using () renaming (String to UString)

-- ==================================================================
-- §0  `Maybe`'s Kleisli composition, spelled out.  The chain's passes
-- are partial, so composing two of them is a bind, and `Section`'s
-- composition below is the only place it is used.
-- ==================================================================

bindMb : {X Y : Type₀} → Maybe X → (X → Maybe Y) → Maybe Y
bindMb (just x) f = f x
bindMb nothing  f = nothing

-- ==================================================================
-- §1  STAGES AND PROJECTIONS.
-- ==================================================================

record Stage : Type₁ where
  field
    Ir   : Type₀
    says : Ir → UString

open Stage public

infix 4 _↘_

-- `B ↘ A` : the stage-B IR projects down to the stage-A IR, faithfully.
record _↘_ (B A : Stage) : Type₀ where
  field
    bwd   : B .Ir → A .Ir
    -- the projection is not observable: it prints the same program
    faith : (b : B .Ir) → A .says (bwd b) ≡ B .says b

open _↘_ public

idProj : {A : Stage} → A ↘ A
idProj .bwd   b = b
idProj .faith b = refl

-- THE CASCADE.  `p ∘↘ q` projects a stage-C object past B and on to A,
-- and its faithfulness is the composite of the two.  Every "project
-- this IR down to an earlier pass" in the chain is an instance.
_∘↘_ : {A B C : Stage} → B ↘ A → C ↘ B → C ↘ A
(p ∘↘ q) .bwd   c = p .bwd (q .bwd c)
(p ∘↘ q) .faith c = p .faith (q .bwd c) ∙ q .faith c

infixr 9 _∘↘_

-- ... and the consequence that is actually used: two objects at
-- DIFFERENT stages are comparable, through what they say.
sameSay : {A B : Stage} (p : B ↘ A) (b b' : B .Ir)
        → A .says (p .bwd b) ≡ A .says (p .bwd b') → B .says b ≡ B .says b'
sameSay p b b' e = sym (p .faith b) ∙ e ∙ p .faith b'

-- ==================================================================
-- §2  PASSES, AND THEIR TWO COHERENCE LAWS.
-- ==================================================================

infix 4 _↗_

record _↗_ (A B : Stage) : Type₀ where
  field
    fwd : A .Ir → Maybe (B .Ir)

open _↗_ public

module _ {A B : Stage} (f : A ↗ B) (p : B ↘ A) where

  -- STRONG: `bwd` is a section of `fwd`.  Print ANY stage-B object and
  -- re-run the pass on the text: that same object comes back.
  Section : Type₀
  Section = (b : B .Ir) → f .fwd (p .bwd b) ≡ just b

  -- WEAK, and the one an ambiguous surface syntax admits: the claim is
  -- made only of objects the pass itself produced.  `fwd ∘ bwd ∘ fwd ≡
  -- fwd`, i.e. `bwd` is a generalised inverse.
  Reflects : Type₀
  Reflects = (a : A .Ir) (b : B .Ir) → f .fwd a ≡ just b → f .fwd (p .bwd b) ≡ just b

  -- the implication, and it is the only one available
  section→reflects : Section → Reflects
  section→reflects sec _ b _ = sec b

-- `Section` composes; `Reflects` does not.  See the header.
compose↗ : {A B C : Stage} → A ↗ B → B ↗ C → A ↗ C
compose↗ f g .fwd a = bindMb (f .fwd a) (g .fwd)

sectionComp : {A B C : Stage} (f : A ↗ B) (p : B ↘ A) (g : B ↗ C) (q : C ↘ B)
            → Section f p → Section g q
            → Section (compose↗ f g) (p ∘↘ q)
sectionComp f p g q sf sg c =
  cong (λ z → bindMb z (g .fwd)) (sf (q .bwd c)) ∙ sg c

-- ==================================================================
-- §3  THE STATEMENT THE CHAIN IS AFTER.
--
-- "Any part of an IR projects down to an earlier pass; the result is
-- not literally the same object, but it elaborates the same."  With the
-- vocabulary above that is one line, and it needs only `Reflects`.
-- ==================================================================

module _ {A B : Stage} (f : A ↗ B) (p : B ↘ A) where

  -- Projecting a stage-B object to stage A and re-running the pass
  -- returns THE SAME OBJECT -- provided the object came from the pass.
  roundTrip : Reflects f p → (a : A .Ir) (b : B .Ir)
            → f .fwd a ≡ just b → f .fwd (p .bwd b) ≡ just b
  roundTrip r = r

  -- ... and, whether or not it does, the projection is observationally
  -- inert: what the earlier stage says of it is what the later stage
  -- said.  This half needs no hypothesis at all.
  inert : (b : B .Ir) → A .says (p .bwd b) ≡ B .says b
  inert = p .faith
