{-
  The four residuals, one per (operation, slot), and what each costs.

  A residual is a grammar AT THE SORT OF ITS SLOT, so focusing `lamOp`
  at its binder gives a grammar over NAMES -- something no single-sorted
  presentation can state.  `⊸ᶠ-β`/`⊸ᶠ-η` are `refl` generically for all
  four, including the two cross-sorted ones.  What is NOT generic is the
  adjunction with the tensor -- see `Adjunctions.agda`.

  Defines the four foci `focFun`/`focBind`/`focBody`/`focVar` and the
  residual each names: `_⟜ᵃ_`, `Binds`, `Under`, `Wraps`.  Proves
  `bind-UP` and `body-UP`, the universal properties at the two
  cross-sorted foci.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Residuals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit

open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base

module Residuals (Name : Type₀) where

  open LamBase Name

  -- (a) the function position of an application: `C ⟜ B`
  focFun : Focus λFib appOp true
  focFun .SplitAt _    = Raw            -- the argument
  focFun .whole {u} v  = app u v
  focFun .Rest         = Unit
  focFun .restOf _     = false
  focFun .restSlot v _ = v

  module F = FocusNotation focFun

  -- `(C ⟜ᵃ B) u` DENOTES: "`u` is a function -- applying it to any `B`
  -- gives a `C`".  Same fixity as the ambient library's `_⟜_`.
  infixl 2 _⟜ᵃ_

  _⟜ᵃ_ : TmG → TmG → TmG
  C ⟜ᵃ B = F.⊸ᶠ (λ b → if b then C else B) C

  -- (b) THE BINDER SLOT: a residual at sort `nm`, i.e. a predicate on
  --     names -- "what a name must satisfy for `λ-. body` to be a whole"
  focBind : Focus λFib lamOp true
  focBind .SplitAt _    = Raw           -- the body
  focBind .whole {n} t  = lam n t
  focBind .Rest         = Unit
  focBind .restOf _     = false
  focBind .restSlot t _ = t

  module B = FocusNotation focBind

  -- `Binds A C n` DENOTES: "binding `n` is enough -- `lam n t` is a `C`
  -- for every body `t` that is an `A`".
  Binds : TmG → TmG → NmG
  Binds A C = B.⊸ᶠ (λ { true → ⊤G ; false → A }) C

  -- (c) the body slot: cross-sorted the other way, complement is a name
  focBody : Focus λFib lamOp false
  focBody .SplitAt _    = Name
  focBody .whole {t} n  = lam n t
  focBody .Rest         = Unit
  focBody .restOf _     = true
  focBody .restSlot n _ = n

  module Y = FocusNotation focBody

  -- `Under P C t` DENOTES: "`t` is a body good under any `P`-binder --
  -- `lam n t` is a `C` for every name `n` satisfying `P`".
  Under : NmG → TmG → TmG
  Under P C = Y.⊸ᶠ (λ { true → P ; false → ⊤G }) C

  -- (d) `varOp` has arity `Unit`, so its slot's complement is EMPTY --
  --     the best-behaved residual here
  focVar : Focus λFib varOp tt
  focVar .SplitAt _   = Unit
  focVar .whole {n} _ = var n
  focVar .Rest        = ⊥
  focVar .restOf ()
  focVar .restSlot _ ()

  module V = FocusNotation focVar

  -- `Wraps C n` DENOTES: "`var n` is a `C`".  The complement is empty,
  -- so nothing else is quantified over.
  Wraps : TmG → NmG
  Wraps C = V.⊸ᶠ (λ _ → ⊤G) C

  -- The universal property is the generic one and is DEFINITIONAL, at
  -- the cross-sorted foci too: nothing about sorts interferes with β/η.
  bind-UP : {A C : TmG}
          → Iso (⊤G ⊢ Binds A C)
                (B.FocusedHom {A = λ { true → ⊤G ; false → A }} {B = C})
  bind-UP {A} {C} = B.⊸ᶠ-UP {A = λ { true → ⊤G ; false → A }} {B = C}

  body-UP : {P : NmG} {C : TmG}
          → Iso (⊤G ⊢ Under P C)
                (Y.FocusedHom {A = λ { true → P ; false → ⊤G }} {B = C})
  body-UP {P} {C} = Y.⊸ᶠ-UP {A = λ { true → P ; false → ⊤G }} {B = C}
