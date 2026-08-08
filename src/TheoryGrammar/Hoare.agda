{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A PROGRAM LOGIC OVER AN ARBITRARY `Fibered`. -}
module TheoryGrammar.Hoare where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesFib
open import TheoryGrammar.CarrierMap

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓD ℓE : Level

-- COMMANDS FROM ONE `Fibered` TO ANOTHER. Same signature and levels, so
-- `pull` and `wp` are comparable below.

module Hoare {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (F G : Fibered σ ℓX ℓP) where

  -- the source's combinators, unqualified; the target's, qualified.
  -- Neither is re-exported, so an instance's own `open RulesF Fib` is
  -- undisturbed.
  open RulesF F
  module Tgt = RulesF G

  private variable s t : S

  -- Commands, and the two images.

  Cmd : (ℓC : Level) → S → S → Type (ℓ-max ℓX (ℓ-suc ℓC))
  Cmd ℓC s t = F .carrier s → G .carrier t → Type ℓC

  -- WEAKEST PRECONDITION -- reindexing along the relation.
  wp : Cmd ℓC s t → Tgt.TheoryTy ℓA t → TheoryTy (ℓ-max ℓX (ℓ-max ℓC ℓA)) s
  wp {t = t} c Q m = (m' : G .carrier t) → c m m' → Q m'

  -- STRONGEST POSTCONDITION -- the direct image.
  sp : Cmd ℓC s t → TheoryTy ℓA s → Tgt.TheoryTy (ℓ-max ℓX (ℓ-max ℓC ℓA)) t
  sp {s = s} c P m' = Σ[ m ∈ F .carrier s ] (P m × c m m')

  -- Functorial in the assertion: this is all `consequence` needs, and
  -- keeping it separate is what makes the rule of consequence a
  -- composite of `_∘g_` rather than a pointful proof.
  wp-map : (c : Cmd ℓC s t) {Q : Tgt.TheoryTy ℓA t} {Q' : Tgt.TheoryTy ℓB t}
         → Q Tgt.⊢ Q' → wp c Q ⊢ wp c Q'
  wp-map c f m w m' r = f m' (w m' r)

  -- PRIMITIVE (phase 1). What blocks a combinator is not the index but
  -- that `sp c P` is a hand-rolled `Σ` rather than a composite of
  -- connectives, so the two sides are only isomorphic and there is nothing
  -- for `⊗ˢ-E` to act on.
  sp-map : (c : Cmd ℓC s t) {P : TheoryTy ℓA s} {P' : TheoryTy ℓB s}
         → P ⊢ P' → sp c P Tgt.⊢ sp c P'
  sp-map c f m' (m , p , r) = m , f m p , r

  -- THE ADJUNCTION `sp c ⊣ wp c`.  Currying and swapping; both round
  -- trips are `refl`, because Σ and Π both have η.

  sp⊣wp : (c : Cmd ℓC s t) (P : TheoryTy ℓA s) (Q : Tgt.TheoryTy ℓB t)
        → Iso (sp c P Tgt.⊢ Q) (P ⊢ wp c Q)
  sp⊣wp c P Q .Iso.fun f m p m' r = f m' (m , p , r)
  sp⊣wp c P Q .Iso.inv g m' (m , p , r) = g m p m' r
  sp⊣wp c P Q .Iso.sec _ = refl
  sp⊣wp c P Q .Iso.ret _ = refl

  -- HOARE TRIPLES are entailments.  Nothing new is introduced.

  ⟪_⟫_⟪_⟫ : TheoryTy ℓA s → Cmd ℓC s t → Tgt.TheoryTy ℓB t
          → Type (ℓ-max ℓX (ℓ-max ℓA (ℓ-max ℓC ℓB)))
  ⟪ P ⟫ c ⟪ Q ⟫ = P ⊢ wp c Q

  -- the rule of consequence, from `∘g` and `wp-map` alone
  consequence : (c : Cmd ℓC s t)
                {P : TheoryTy ℓA s} {P' : TheoryTy ℓB s}
                {Q : Tgt.TheoryTy ℓD t} {Q' : Tgt.TheoryTy ℓE t}
              → P' ⊢ P → Q Tgt.⊢ Q' → ⟪ P ⟫ c ⟪ Q ⟫ → ⟪ P' ⟫ c ⟪ Q' ⟫
  consequence c pre post tr = wp-map c post ∘g tr ∘g pre

  -- A DETERMINISTIC COMMAND IS A FUNCTION, AND `wp` AT ONE IS THE
  -- CARTESIAN LIFT.

  fn : (F .carrier s → G .carrier t) → Cmd ℓX s t
  fn f m m' = m' Eq.≡ f m

  wp-fn-repr : (f : F .carrier s → G .carrier t) (Q : Tgt.TheoryTy ℓA t)
               (m : F .carrier s)
             → wp (fn f) Q m ≡ (Tgt.⌈ f m ⌉ Tgt.⊢ Q)
  wp-fn-repr f Q m = refl

  wp-fn : (f : F .carrier s → G .carrier t) (Q : Tgt.TheoryTy ℓA t)
          (m : F .carrier s)
        → Iso (wp (fn f) Q m) (Q (f m))
  wp-fn f Q m = Tgt.⌈⌉-UP {a = f m} {B = Q}

  -- LOCALITY AND THE FRAME RULE, at one operation.

  module Frame (o : σ .ops) where

    -- one command per slot.  The classical rule is the instance where
    -- all but one of them is `skip`; see `Endo` and the header (3).
    SlotCmd : (ℓD : Level) → Type (ℓ-max ℓ' (ℓ-max ℓX (ℓ-suc ℓD)))
    SlotCmd ℓD = (a : σ .arities o) → Cmd ℓD (σ .sortOf o a) (σ .sortOf o a)

    -- LOCALITY. A splitting of the INPUT yields a splitting of the OUTPUT,
    -- slotwise related by the slot commands.

    Local : Cmd ℓC (σ .resultSort o) (σ .resultSort o) → SlotCmd ℓD
          → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓC ℓD))))
    Local c d =
      (m : F .carrier (σ .resultSort o)) (sl : F .Split o m)
      (m' : G .carrier (σ .resultSort o)) → c m m'
      → Σ[ sl' ∈ G .Split o m' ]
          ((a : σ .arities o) → d a (F .parts o m sl a) (G .parts o m' sl' a))

    -- THE FRAME RULE. `⊗ˢ-E` consumes the tensor, locality moves the
    -- splitting across the command, `⊗ˢ-I` rebuilds it at the output.

    frame-wp : (c : Cmd ℓC (σ .resultSort o) (σ .resultSort o)) (d : SlotCmd ℓD)
             → Local c d
             → (B : (a : σ .arities o) → Tgt.TheoryTy ℓA (σ .sortOf o a))
             → ⊗ˢ o (λ a → wp (d a) (B a)) ⊢ wp c (Tgt.⊗ˢ o B)
    frame-wp c d loc B =
      ⊗ˢ-E o {A = λ a → wp (d a) (B a)} {B = wp c (Tgt.⊗ˢ o B)}
        (λ m sl k m' r →
          Tgt.⊗ˢ-I o {A = B} m' (loc m sl m' r .fst)
            (λ a → k a (G .parts o m' (loc m sl m' r .fst) a)
                       (loc m sl m' r .snd a)))

    -- ... and its packaging as the composition of a FAMILY OF TRIPLES,
    -- which is the form an instance uses: `⊗ˢ-map` feeds the slotwise
    -- triples in, `frame-wp` does the rest.
    frame-cmd : (c : Cmd ℓC (σ .resultSort o) (σ .resultSort o)) (d : SlotCmd ℓD)
          → Local c d
          → {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
            {B : (a : σ .arities o) → Tgt.TheoryTy ℓB (σ .sortOf o a)}
          → ((a : σ .arities o) → ⟪ A a ⟫ d a ⟪ B a ⟫)
          → ⟪ ⊗ˢ o A ⟫ c ⟪ Tgt.⊗ˢ o B ⟫
    frame-cmd c d loc {A = A} {B = B} k =
      frame-wp c d loc B ∘g ⊗ˢ-map o {A = A} {B = λ a → wp (d a) (B a)} k

-- THE ENDO CASE -- a command on one `Fibered` -- with `skip`.

module Endo {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open Hoare Fib Fib public
  open RulesF Fib

  private variable s : S

  skip : Cmd ℓX s s
  skip = fn (λ m → m)

  wp-skip : (Q : TheoryTy ℓA s) (m : Fib .carrier s) → Iso (wp skip Q m) (Q m)
  wp-skip Q = wp-fn (λ m → m) Q

  -- the two directions as terms of the calculus.  `skip-I` is `⌈⌉-E`:
  -- `wp skip Q m` IS `⌈ m ⌉ ⊢ Q`.
  skip-I : (Q : TheoryTy ℓA s) → Q ⊢ wp skip Q
  skip-I Q m q = ⌈⌉-E q

  skip-E : (Q : TheoryTy ℓA s) → wp skip Q ⊢ Q
  skip-E Q m w = w m Eq.refl

  -- `skip` is local at every operation, and the splitting it hands back
  -- is the one it was given.
  module _ (o : σ .ops) where

    open Frame o

    skipLocal : Local (skip {σ .resultSort o}) (λ a → skip)
    skipLocal m sl .m Eq.refl = sl , λ a → Eq.refl

-- `wp` VERSUS `pull`: the Cartesian lift, and `push⊗` as an instance of
-- the frame rule.

module ReindexHoare {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                    {F G : Fibered σ ℓX ℓP} (h : Reindex F G) where

  open Hoare F G
  open RulesF F
  module A = Along h
  module Bwd = Hoare G F          -- commands the other way, for `Reflects`

  -- the deterministic command induced by `h`, at each sort
  cmd : (s : S) → Cmd ℓX s s
  cmd s = fn (h .hom s)

  -- THE SHARPEST STATEMENT: `wp` along a function IS `pull`.

  wp-pull : (s : S) (B : Tgt.TheoryTy ℓA s) (m : F .carrier s)
          → Iso (wp (cmd s) B m) (A.pull B m)
  wp-pull s B m = wp-fn (h .hom s) B m

  wp→pull : (s : S) (B : Tgt.TheoryTy ℓA s) → wp (cmd s) B ⊢ A.pull B
  wp→pull s B m w = Iso.fun (wp-pull s B m) w

  pull→wp : (s : S) (B : Tgt.TheoryTy ℓA s) → A.pull B ⊢ wp (cmd s) B
  pull→wp s B m q = Iso.inv (wp-pull s B m) q

  module _ (o : σ .ops) where

    open Frame o
    module BwdFr = Bwd.Frame o

    -- `SplitPresAt` IS `Local`, for the deterministic command.  Note
    -- there is no coercion and no `Eq.sym`: `homParts` has exactly the
    -- orientation `fn` asks for.

    Local-of-SplitPres : SplitPresAt h o
                       → Local (cmd (σ .resultSort o)) (λ a → cmd (σ .sortOf o a))
    Local-of-SplitPres P m sl .(h .hom _ m) Eq.refl =
      P .homSplit m sl , λ a → P .homParts m sl a

    -- ... hence `push⊗` is the frame rule at a deterministic command.

    push⊗-from-frame : (P : SplitPresAt h o)
                       (B : (a : σ .arities o) → Tgt.TheoryTy ℓA (σ .sortOf o a))
                     → ⊗ˢ o (λ a → A.pull (B a)) ⊢ A.pull (Tgt.⊗ˢ o B)
    push⊗-from-frame P B =
        wp→pull (σ .resultSort o) (Tgt.⊗ˢ o B)
      ∘g frame-wp (cmd (σ .resultSort o)) (λ a → cmd (σ .sortOf o a))
                  (Local-of-SplitPres P) B
      ∘g ⊗ˢ-map o {A = λ a → A.pull (B a)}
                  {B = λ a → wp (cmd (σ .sortOf o a)) (B a)}
                  (λ a → pull→wp (σ .sortOf o a) (B a))

    -- THE TRANSPOSITION.  `ReflectsSplitAt` is `Local` of the CONVERSE
    -- command, read in `Hoare G F`.  The two Σ-types are the same type,
    -- so both directions are pure currying.

    revCmd : (s : S) → Bwd.Cmd ℓX s s
    revCmd s m' m = m' Eq.≡ h .hom s m

    Local-of-Reflects : A.ReflectsSplitAt o
                      → BwdFr.Local (revCmd (σ .resultSort o))
                                    (λ a → revCmd (σ .sortOf o a))
    Local-of-Reflects R .(h .hom _ m) sl' m Eq.refl = R m sl'

    Reflects-of-Local : BwdFr.Local (revCmd (σ .resultSort o))
                                    (λ a → revCmd (σ .sortOf o a))
                      → A.ReflectsSplitAt o
    Reflects-of-Local L m sl' = L (h .hom _ m) sl' m Eq.refl

    -- `pull⊗` is then immediate.  It is NOT an instance of `frame-wp`:
    -- `wp` along the converse of `h` is the pushforward `Π_h`, not
    -- `pull`, so the converse frame rule is a different statement.
    pull⊗-from-Local : BwdFr.Local (revCmd (σ .resultSort o))
                                   (λ a → revCmd (σ .sortOf o a))
                     → (B : (a : σ .arities o) → Tgt.TheoryTy ℓA (σ .sortOf o a))
                     → A.pull (Tgt.⊗ˢ o B) ⊢ ⊗ˢ o (λ a → A.pull (B a))
    pull⊗-from-Local L B = A.pull⊗ o (Reflects-of-Local L) {B = B}
