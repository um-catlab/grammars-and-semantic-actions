{- The box modality □ packaged as an *upstream* (cubical-categorical-logic)
   `Comonad` over the category |GRAMMAR| of SetGrammars and Terms.

   The grammar library already has a bespoke, level-fixed semantic comonad
   `□-Comonad : Grammar.Comonad.Base.Comonad ℓ` (an F₀/F₁ on raw grammars with
   counit ε□ and comultiplication δ).  Here we re-package that data as a genuine
   `Cubical.Categories.Comonad.Base.Comonad (|GRAMMAR| ℓ)`:

     • a c-c-l `Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)` whose action on objects is
       `A ↦ □ ⟨A⟩` (with the requisite `isSetGrammar (□ ⟨A⟩)`, derived below),
       and whose action on morphisms is the bespoke `map□`;
     • an `IsComonad` whose ε/δ are the bespoke ε□/δ assembled into `NatTrans`,
       whose naturality `N-hom`s come from the bespoke `ε-nat`/`δ-nat`, and whose
       comonad laws `idl-δ`/`idr-δ`/`assoc-δ` come from the bespoke
       `counit-l`/`counit-r`/`coassoc`.

   STATUS: the packaging is GREEN.  The Functor (□F), the isSetGrammar (□ ⟨A⟩)
   derivation, the ε/δ NatTrans (incl. their N-hom naturalities), and
   idl-δ/idr-δ all typecheck on the nose from the bespoke data.  The *only* gap
   is `assoc-δ`, which is `sym □-coassoc`; and `□-coassoc` is itself unfinished
   on the `box` branch because it depends on the √l-cat pentagon
   `√l-cat-assoc`, whose deepest C-element PathP is an interactive `{!!}` in
   Grammar.Box.Properties (≈ line 725).  So `assoc-δ` is a hole *because the box
   branch is unfinished*, not because of any packaging obstruction.

   IMPORT NOTE: because Grammar.Box.Properties currently carries an open
   interaction point (`{!!}`), Agda refuses to import it (and hence to load this
   module — exactly as it refuses to load the bespoke Grammar.Box.Comonad) until
   that interaction point is closed *or* Grammar.Box.Properties is given
   `{-# OPTIONS --allow-unsolved-metas #-}`.  This module was verified to
   typecheck cleanly (no errors, no metas of its own) once the upstream
   interaction point is tolerated; the `--allow-unsolved-metas` here covers the
   single inherited `√l-cat-assoc`/`coassoc` meta. -}
{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Categorical.Comonad (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor renaming (𝟙⟨_⟩ to funcId)
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Comonad.Base

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Top Alphabet
open import Grammar.String Alphabet
open import Grammar.Product Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Function Alphabet
open import Grammar.Derivative.String Alphabet
open import Grammar.Box.Base Alphabet
open import Grammar.Box.Properties Alphabet
open import Grammar.Box.Comonad Alphabet using (□-Comonad)
import Grammar.Comonad.Base Alphabet as Bespoke
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

--------------------------------------------------------------------------------
-- isSetGrammar (□ A)
--
-- □ A = &[ w ] √l-string w A, and √l-string w A = (⌈w⌉⊗⊤) ⇒ (⌈w⌉⊗A) (a plain
-- definition).  So:  &ᴰ of sets is a set (isSetGrammar&ᴰ); ⇒ into a set is a set
-- (isSetGrammar⇒, below); ⌈w⌉⊗A is a set (isSetGrammar⊗) since ⌈w⌉ is a language.
--------------------------------------------------------------------------------

opaque
  unfolding _⇒_
  isSetGrammar⇒ : ∀ {ℓA ℓB} {A : Grammar ℓA} {B : Grammar ℓB}
    → isSetGrammar B → isSetGrammar (A ⇒ B)
  isSetGrammar⇒ isSetB w = isSet→ (isSetB w)

isSetGrammar√l-string : ∀ {ℓA} {A : Grammar ℓA} (w : String)
  → isSetGrammar A → isSetGrammar (√l-string w A)
isSetGrammar√l-string {A = A} w isSetA =
  isSetGrammar⇒
    (isSetGrammar⊗ (isLang→isSetGrammar (isLang⌈⌉ w)) isSetA)

isSetGrammar□ : ∀ {ℓA} {A : Grammar ℓA}
  → isSetGrammar A → isSetGrammar (□ A)
isSetGrammar□ {A = A} isSetA =
  isSetGrammar&ᴰ (λ w → isSetGrammar√l-string w isSetA)

--------------------------------------------------------------------------------
-- The endofunctor □ : |GRAMMAR| ℓ → |GRAMMAR| ℓ
--
-- F-ob packages □ ⟨A⟩ as a SetGrammar; F-hom = map□; F-id/F-seq from the
-- bespoke map□-id/map□-seq.  Note ⋆⟨ |GRAMMAR| ⟩ = Term.seq reverses
-- composition, so F-seq f g : map□ (g ∘g f) ≡ map□ g ∘g map□ f, which is
-- exactly map□-seq f g.
--------------------------------------------------------------------------------

module _ {ℓ} where
  -- The bespoke semantic comonad's structure, accessed qualified to avoid the
  -- ε/δ name-clash with Grammar.Box.Base (ε□/δ) and the record's own ε/δ.
  module D = Bespoke.Comonad (□-Comonad {ℓ})

  □F : Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)
  □F .Functor.F-ob A = □ ⟨ A ⟩ , isSetGrammar□ (A .snd)
  □F .Functor.F-hom f = map□ f
  □F .Functor.F-id = map□-id
  □F .Functor.F-seq f g = map□-seq f g

--------------------------------------------------------------------------------
-- ε and δ as natural transformations
--
-- N-hom for ε : NatTrans □F (funcId) is  ε□ ∘g map□ f ≡ f ∘g ε□  (the ⋆-order in
-- |GRAMMAR| reverses ∘g), i.e. sym (ε-nat f).
-- N-hom for δ : NatTrans □F (□F ∘F □F) is  δ ∘g map□ f ≡ map□ (map□ f) ∘g δ,
-- which is exactly δ-nat f.
--------------------------------------------------------------------------------

  εTrans : NatTrans □F (funcId (|GRAMMAR| ℓ))
  εTrans .NatTrans.N-ob A = ε□
  εTrans .NatTrans.N-hom f = sym (D.ε-nat f)

  δTrans : NatTrans □F (funcComp □F □F)
  δTrans .NatTrans.N-ob A = δ
  δTrans .NatTrans.N-hom f = D.δ-nat f

--------------------------------------------------------------------------------
-- The IsComonad structure
--
-- idl-δ / idr-δ are PathPs over the functor-unit coherences F-rUnit / F-lUnit
-- (only the codomain functor varies; the domain stays □F).  We build them with
-- makeNatTransPathP: the N-ob PathP is over a constant object-family (both
-- funcComp □F (funcId) and □F send A ↦ □⟨A⟩), so it degenerates to the plain
-- grammar equalities counit-l / counit-r.
--
-- Concretely, unfolding the whiskerings and ∘ᵛ (= compTrans, which reverses to
-- seqTrans, and ⋆⟨|GRAMMAR|⟩ reverses to ∘g):
--   ((ε ∘ˡ □F) ∘ᵛ δ) ⟦A⟧ = ε□ {□⟨A⟩} ∘g δ      ≡ id   (counit-l)
--   ((□F ∘ʳ ε) ∘ᵛ δ) ⟦A⟧ = map□ ε□ ∘g δ         ≡ id   (counit-r)
-- and pointwise
--   ((□F ∘ʳ δ) ∘ᵛ δ) ⟦A⟧ = map□ δ ∘g δ
--   ((δ ∘ˡ □F) ∘ᵛ δ) ⟦A⟧ = δ ∘g δ
-- so assoc-δ : map□ δ ∘g δ ≡ δ ∘g δ, i.e. sym coassoc.
--------------------------------------------------------------------------------

  □-IsComonad : IsComonad □F
  □-IsComonad .IsComonad.ε = εTrans
  □-IsComonad .IsComonad.δ = δTrans
  □-IsComonad .IsComonad.idl-δ =
    makeNatTransPathP (λ _ → □F) (λ i → F-rUnit {F = □F} i)
      (funExt (λ A → D.counit-l))
  □-IsComonad .IsComonad.idr-δ =
    makeNatTransPathP (λ _ → □F) (λ i → F-lUnit {F = □F} i)
      (funExt (λ A → D.counit-r))
  -- assoc-δ ≡ sym coassoc.  Box-branch-unfinished: coassoc bottoms out at the
  -- √l-cat-assoc pentagon hole in Grammar.Box.Properties (line ~725).
  □-IsComonad .IsComonad.assoc-δ {c = A} = sym D.coassoc

  □-Comonad-c-c-l : Comonad (|GRAMMAR| ℓ)
  □-Comonad-c-c-l = □F , □-IsComonad

--------------------------------------------------------------------------------
-- Remark on the later modality ▷.
--
-- The guarded later modality ▷ (Grammar.Box.GuardedFixpoint / Grammar.Later) is
-- a covariant endofunctor on grammars, so it could be packaged as a c-c-l
-- `Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)` in exactly the same way as □F above.
-- It is, however, NOT a comonad: there is no counit ▷ A ⊢ A (a value "available
-- one step later" cannot be read off now).  It carries the dual `next : A ⊢ ▷ A`
-- and a Löb fixpoint, which make it (with a suitable structure) a *pointed*
-- functor / the basis of a guarded-recursion modality — not a `Comonad`.  So ▷
-- does not yield a `Comonad (|GRAMMAR| ℓ)`.
--------------------------------------------------------------------------------
