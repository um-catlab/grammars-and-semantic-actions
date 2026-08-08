{-# OPTIONS --lossy-unification #-}
{-
  ORDERED CHOICE -- PEG's `A / B` -- AND WHY IT IS DETERMINISTIC.

  A parsing-expression grammar's `A / B` reads "parse an `A`; if that
  FAILS, parse a `B`".  The failure has to be evidence, which is what
  `Inductive.Dual` built: refutations are data.  So ordered choice is not
  a new connective, it is a definition:

      A / B  :=  A ⊕ (A⁻ & B)

  -- "either this is an `A`, or it is REFUTED as an `A` and it is a `B`".
  Both disjuncts are grammars, `&` is additive so both conjuncts see the
  same resource, and `A⁻` carries the reason the first branch failed.

  ==================================================================
  THE POINT: DETERMINISM IS A THEOREM, NOT A CONVENTION.

  In an operational presentation "try `A` first" is a statement about the
  IMPLEMENTATION, and the grammar is ambiguous until you fix a strategy.
  Here the two branches are provably exclusive --

      choice-excl : (A & (A⁻ & B)) ⊢ ⊥G

  -- from nothing but `A & A⁻ ⊢ ⊥`, which `Inductive.Consistent.excl-μ`
  supplies for any guarded description.  So `/` is unambiguous whatever
  order an implementation tries, and `Decidable.Additive.Decision` is the
  record that says so.

  ==================================================================
  STRATIFICATION, AND WHERE IT BITES.

  `A⁻` must exist, i.e. `A` must have a refutation grammar.  For
  `A = μ F` that is `Inductive.Dual.μ⁻ F`, and the exclusion is
  `Inductive.Consistent.excludeμ` ON THE NOSE:

      excludeμ : (x) (m) → μ F (x , m) × μ⁻ F (x , m) → ⊥*
      choice-Decision's hypothesis :  (A & A⁻) ⊢ ⊥G

  and `(A & A⁻) ⊢ ⊥G` unfolds to `(m) → A m × A⁻ m → ⊥G m` with
  `⊥G m = ⊥*`.  So PEG's ordered choice is unambiguous for EVERY guarded
  description, with no work beyond T2 -- which is what made T2 worth
  proving separately from the decision procedure.  What this file cannot do is self-referential negation:
  `A / B` where `A`'s own definition mentions this choice.  That is
  Atkey's `Liar`, it needs the Gelfond-Lifschitz reduct and an
  alternating fixed point, and it admits a third truth value.

  A parser that may answer "don't know" is a semantics, not a tool, so
  the restriction is one to WANT rather than tolerate -- which is also
  why every real PEG implementation rejects left recursion.

  PRIMITIVE: none.
-}
module TheoryGrammar.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Base
open import TheoryGrammar.Rules
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓX ℓA ℓB ℓC : Level

module Choose {S : Type ℓS} (Car : S → Type ℓX) where

  open DecAdd Car public

  private variable s : S

  -- THE CONNECTIVE.  A definition, not a new former.

  Choice : (A A⁻ B : TheoryTy ℓA s) → TheoryTy ℓA s
  Choice A A⁻ B = A ⊕ (A⁻ & B)

  -- the two introductions, as terms
  choice-fst : {A A⁻ B : TheoryTy ℓA s} → A ⊢ Choice A A⁻ B
  choice-fst {A = A} {A⁻} {B} = ⊕-I₁ {A = A} {B = A⁻ & B}

  choice-snd : {A A⁻ B : TheoryTy ℓA s} → (A⁻ & B) ⊢ Choice A A⁻ B
  choice-snd {A = A} {A⁻} {B} = ⊕-I₂ {B = A⁻ & B} {A = A}

  -- ... and the elimination, which is `⊕-E` and nothing else
  choice-E : {A A⁻ B : TheoryTy ℓA s} {C : TheoryTy ℓC s}
           → A ⊢ C → (A⁻ & B) ⊢ C → Choice A A⁻ B ⊢ C
  choice-E = ⊕-E

  -- THE THEOREM.  Ordered choice is UNAMBIGUOUS, and the whole proof is
  -- the exclusion of `A` from its own refutation.

  choice-excl : {A A⁻ B : TheoryTy ℓA s}
              → (A & A⁻) ⊢ ⊥G
              → (A & (A⁻ & B)) ⊢ ⊥G
  choice-excl excl m (a , (k , _)) = excl m (a , k)

  -- ... packaged. `Decision A (A⁻ & B)` says the two branches of `/` are
  -- exclusive AND that one of them holds -- so a decision procedure for `A
  -- / B` is a decision between its branches, with no appeal to which one
  -- an implementation tried first.
  choice-Decision : {A A⁻ B : TheoryTy ℓA s}
                  → (A & A⁻) ⊢ ⊥G
                  → ⊤G ⊢ Choice A A⁻ B
                  → Decision A (A⁻ & B)
  choice-Decision excl total .Decision.decide  = total
  choice-Decision excl total .Decision.exclude = choice-excl excl

  -- ASSOCIATIVITY OF THE FIRST BRANCH -- i.e. `(A / B) / C` and
  -- `A / (B / C)` agree on their FIRST alternative, which is the part
  -- ordered choice actually constrains.  One `⊕`-shuffle each way.

  choice-assoc→ : {A A⁻ B C : TheoryTy ℓA s}
                → A ⊢ Choice A A⁻ (Choice B B C)
  choice-assoc→ {A = A} {A⁻} {B} {C} = choice-fst {A = A} {A⁻} {Choice B B C}
