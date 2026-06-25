{- The box modality □ as the comonad of the presheaf/families adjunction over
   the suffix category.

   PREVIOUSLY this module re-packaged gsa's bespoke, hand-built semantic comonad
   `Grammar.Box.Comonad.□-Comonad` (the `&[ w ] √l-string w A` construction) as a
   `Cubical.Categories.Comonad.Base.Comonad (|GRAMMAR| ℓ)`.  That packaging had an
   irreducible `assoc-δ` hole inherited from the unfinished √l-cat pentagon
   `√l-cat-assoc` in `Grammar.Box.Properties`, and so required
   `--allow-unsolved-metas`.

   This module REPLACES that approach.  The box modality `□` is now *inherited*
   from upstream (cubical-categorical-logic) as the comonad of the
   presheaf/families adjunction over the *suffix category* of strings.  No
   `Grammar.Box.*` is imported, and the comonad laws are FREE from the
   adjunction: there is no pentagon hole anymore, and no `--allow-unsolved-metas`.

   THE CONSTRUCTION (all upstream, instantiated at the gsa alphabet):

     • The suffix category `SuffixCat` (Cubical.Categories.Direct.Instances.Suffix)
       has objects `List ⟨Alphabet⟩ = String` and Hom y x = `y ≤ˢ x` (the
       reflexive suffix order).

     • Cubical.Categories.Presheaf.Family.Base provides, for any base category C:
         - `Psh→Fam : Functor Psh Fam`   where `Fam = PowerCategory C.ob (SET _)`
           and `Psh = PRESHEAF C _`;
         - `Cofree : Functor Fam Psh` with
             `Cofree A x = (y : C.ob) → C.Hom[ y , x ] → A y .fst`,
           i.e. `Cofree A x = ∀ (y suffix-of x). A y` — this IS `□`;
         - the adjunction `CofreeFamAdj : Psh→Fam ⊣ Cofree`.

     • `Wᶜ = Psh→Fam ∘F Cofree : Functor Fam Fam` is the comonad endofunctor `□`
       on families.  Its comonad structure is presented as a *monad on Fam ^op*,
       via `MonadFromAdjunction` applied to the opposite adjunction:
         `mᶜ : IsMonad ((Psh→Fam ^opF) ∘F (Cofree ^opF))`.
       The comonad laws are thus exactly the (free) monad laws of `mᶜ` — no
       coassociativity is proved by hand.

   We expose the comonad as an `ExtensionSystem` on `Fam` (a comonad on `Fam` in
   the extension-system sense is a monad on `Fam ^op`:
   `Comonad.ExtensionSystem.ExtensionSystem Fam = MES.ExtensionSystem (Fam ^op)`),
   obtained from `mᶜ` by the total function `Monad→ExtensionSystem`.  Zero glue,
   zero holes.

   STATUS: GREEN.  No holes, no postulates, no `--allow-unsolved-metas`, no
   `Grammar.Box.*` import.

   REMARK on `Fam` vs gsa's `|GRAMMAR|`.  `Fam.ob = String → SET ℓ` whereas gsa's
   `SetGrammar ℓ = Σ[ A ∈ (String → Type ℓ) ] (∀ w → isSet (A w))`.  These are
   equivalent by the Π↔Σ swap (a family of sets ≅ a set-valued family), but NOT
   definitionally equal, so we work natively on `Fam`.  Transporting the comonad
   along `Fam ≃ |GRAMMAR|` is possible but heavy and unnecessary for the headline
   result; we record the iso only as this remark. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Categorical.Comonad (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint using (opositeAdjunction ; module UnitCounit)
open UnitCounit using (_⊣_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Presheaf.StrictHom.Base using (PRESHEAF)
open import Cubical.Categories.Monad.Base using (IsMonad ; Monad)
open import Cubical.Categories.Adjoint.Monad using (MonadFromAdjunction)
open import Cubical.Categories.Monad.ExtensionSystem
  using (Monad→ExtensionSystem)
import Cubical.Categories.Comonad.ExtensionSystem as CoES

open import Cubical.Categories.Direct.Instances.Suffix
  (⟨ Alphabet ⟩) (str Alphabet)
  using (SuffixCat)
import Cubical.Categories.Presheaf.Family.Base as Family

open import Grammar.Base Alphabet using (String)

private
  variable
    ℓ : Level

--------------------------------------------------------------------------------
-- The categories Fam and Psh over the suffix category.
--
--   SuffixCat.ob = List ⟨Alphabet⟩ = String   (definitionally gsa's `String`).
--   Fam = PowerCategory String (SET ℓ) = String → SET ℓ.
--   Psh = PRESHEAF SuffixCat ℓ.
--------------------------------------------------------------------------------

module _ (ℓ : Level) where
  open Category

  Fam : Category (ℓ-suc ℓ) ℓ
  Fam = PowerCategory (SuffixCat .ob) (SET ℓ)

  Psh : Category _ _
  Psh = PRESHEAF SuffixCat ℓ

--------------------------------------------------------------------------------
-- The presheaf/families adjunction, instantiated at SuffixCat.
--
-- These are the *exposed* names of Cubical.Categories.Presheaf.Family.Base; the
-- file's own `Fam`/`Psh`/`Wᶜ`/`mᶜ` are private, so we reconstruct the comonad
-- functor and its monad-on-the-opposite presentation from the public data.
--------------------------------------------------------------------------------

module _ {ℓ : Level} where
  Psh→Fam : Functor (Psh ℓ) (Fam ℓ)
  Psh→Fam = Family.Psh→Fam {ℓ = ℓ} SuffixCat

  -- Cofree A x = ∀ (y suffix-of x). A y      -- this IS □ on families.
  Cofree : Functor (Fam ℓ) (Psh ℓ)
  Cofree = Family.Cofree {ℓ = ℓ} SuffixCat

  CofreeFamAdj : Psh→Fam ⊣ Cofree
  CofreeFamAdj = Family.CofreeFamAdj {ℓ = ℓ} SuffixCat

  -- The comonad endofunctor □ = Wᶜ on families.
  Wᶜ : Functor (Fam ℓ) (Fam ℓ)
  Wᶜ = Psh→Fam ∘F Cofree

  -- The comonad presented as a monad on Fam ^op.  THIS is where the comonad
  -- laws come from (free from the adjunction); we never prove coassociativity.
  mᶜ : IsMonad ((Psh→Fam ^opF) ∘F (Cofree ^opF))
  mᶜ = MonadFromAdjunction (Cofree ^opF) (Psh→Fam ^opF)
         (opositeAdjunction CofreeFamAdj)

  -- Package as a Monad on Fam ^op …
  monadᶜ : Monad ((Fam ℓ) ^op)
  monadᶜ = ((Psh→Fam ^opF) ∘F (Cofree ^opF)) , mᶜ

  -- … which is exactly a comonad on Fam in the extension-system sense:
  --   Comonad.ExtensionSystem.ExtensionSystem (Fam ℓ)
  --     = Monad.ExtensionSystem.ExtensionSystem ((Fam ℓ) ^op).
  -- Monad→ExtensionSystem is a total function, so this is free of any proof
  -- obligation: the comonad laws are inherited verbatim from the adjunction.
  □Comonad : CoES.ExtensionSystem (Fam ℓ)
  □Comonad = Monad→ExtensionSystem ((Fam ℓ) ^op) monadᶜ

  --------------------------------------------------------------------------------
  -- The box modality □ on families.
  --
  -- □ = Wᶜ .F-ob, and definitionally
  --     □ A x = (y : String) → SuffixCat[ y , x ] → A y .fst
  --           = ∀ (y suffix-of x). A y.
  -- This REPLACES gsa's manual `Grammar.Box` (the `&[ w ] √l-string w A`
  -- construction): the same box modality now arises uniformly as the cofree
  -- comonad of the suffix-category presheaf/families adjunction.
  --------------------------------------------------------------------------------

  □ : (Fam ℓ) .Category.ob → (Fam ℓ) .Category.ob
  □ = Wᶜ .Functor.F-ob

--------------------------------------------------------------------------------
-- Comonadicity comparison (the headline equivalence).
--
-- Presheaves over the suffix order are exactly the □-coalgebras: the comparison
-- functor `Psh→COALG : Functor Psh COALG` (into the co-Eilenberg–Moore category
-- of the comonad) is an equivalence.  We re-export the comparison and the full
-- equivalence from upstream.
--------------------------------------------------------------------------------

module _ {ℓ : Level} where
  -- COALG = co-Eilenberg–Moore category of the □ comonad on Fam.
  COALG : Category _ _
  COALG = Family.COALG {ℓ = ℓ} SuffixCat

  -- The comparison functor: presheaves over the suffix order → □-coalgebras.
  Psh→COALG : Functor (Psh ℓ) COALG
  Psh→COALG = Family.Psh→COALG {ℓ = ℓ} SuffixCat

  -- Comonadicity: Psh ≃ □-coalgebras.
  open import Cubical.Categories.Equivalence using (_≃ᶜ_)
  Psh≃COALG : (Psh ℓ) ≃ᶜ COALG
  Psh≃COALG = Family.Psh≃COALG {ℓ = ℓ} SuffixCat

--------------------------------------------------------------------------------
-- Remark on the later modality ▷.
--
-- The guarded later modality ▷ is a covariant endofunctor on grammars and could
-- be packaged as a c-c-l `Functor`, but it is NOT a comonad: there is no counit
-- ▷ A ⊢ A.  It carries the dual `next : A ⊢ ▷ A` and a Löb fixpoint, making it a
-- *pointed* functor / the basis of a guarded-recursion modality — not a comonad.
--------------------------------------------------------------------------------
