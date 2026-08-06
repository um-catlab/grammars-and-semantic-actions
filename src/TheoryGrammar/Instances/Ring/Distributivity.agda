{-
  DISTRIBUTIVITY IS A LAX MAP, AND IT IS INVERTIBLE EXACTLY ON PRECISE
  ARGUMENTS.

  The wanted statement is

      distrib :  A ⊗× (B ⊗₊ C)  ⊢  (A ⊗× B) ⊗₊ (A ⊗× C)

  -- the Dirichlet product distributing over the Cauchy product, i.e.
  the connective form of `x(y+z) = xy + xz`.

  ------------------------------------------------------------------
  1.  WHY IT DOES NOT COME FROM `eqn→Iso`.

  `TheoryGrammar.Equations` lifts an equation of the theory to an
  ISOMORPHISM of composite connectives, and the header of that file
  states the side condition exactly: the terms must be LINEAR, each
  variable used exactly once.  The mechanism is that for a linear term
  the nested convolution FLATTENS --

      ⟪ t ⟫ A m  =  Σ (valuation ρ) . (eval ρ t = m) × Π_v A_v (ρ v)

  -- so `⟪ t ⟫` depends on `t` only through the function `eval t`, and
  equal denotations give equal connectives.

  `x(y + z) = xy + xz` is NOT linear: `x` occurs twice on the right.
  Concretely, `⟪ x(y+z) ⟫` and `⟪ xy + xz ⟫` are

      Σ (ρx, ρy, ρz) . ρx·(ρy+ρz) = n . A ρx × B ρy × C ρz
      Σ (ρx, ρy, ρz) . ρx·ρy + ρx·ρz = n . A ρx × B ρy × C ρz

  and these ARE isomorphic -- but only because the flattening already
  identified the two occurrences of `x` by hand.  The connective we
  actually want on the right is the NESTED composite
  `(A ⊗× B) ⊗₊ (A ⊗× C)`, whose flattening has FOUR variables
  (x₁,y,x₂,z) and does not constrain `x₁ = x₂`.  The flattening theorem
  gives no map between a three-variable and a four-variable shape, so
  `eqn→Iso` is simply not applicable.  A `distrib` must be built by
  hand, and its content is exactly the diagonal `x ↦ (x,x)` that
  linearity forbids.

  ------------------------------------------------------------------
  2.  WHAT IS ACTUALLY TRUE, AND A NEGATIVE FINDING ABOUT THE FRAMEWORK.

  The forward map `distrib` exists for EVERY A.  This is worth saying
  plainly, because the "linear logic" reading predicts otherwise: it
  needs `A i` twice, and it simply uses the Agda variable twice.  The
  substructural discipline of this calculus lives entirely in the INDEX
  -- `_⊢_` preserves it and `⊗ˢ` splits it -- and not at all in the
  PAYLOAD, which is an ordinary type in a cartesian metatheory.  So
  "A cannot be duplicated" is false here, and a `Dup A` / ⊗-comonoid
  hypothesis on the forward map would be vacuous.  The linearity that
  the framework does enforce is resource-linearity in `m`, which is the
  half that matters for parsing; contraction on payloads is free.

  What fails is INVERTIBILITY.  Given a point of the right-hand side we
  have two independent factorisations, `i₁ · p = u` and `i₂ · q = v`,
  with an `A i₁` and an `A i₂`, and no reason for `i₁ = i₂`.  So

      distrib is a LAX structure map, not an isomorphism,

  and it is the ⊗/⅋ situation of linear logic rather than the ⊗/⊕ one.

  ------------------------------------------------------------------
  3.  THE MODALITY THAT REPAIRS IT IS PRECISION, NOT DUPLICABILITY.

  To invert, all that is needed is that `A` PINS ITS INDEX:

      Precise A  =  (A i → A j → i ≡ j)  together with  isProp (A i)

  -- the separation-logic notion of a precise predicate, and the
  internal statement of "A is subterminal in the slice".  Then
  `i₁ = i₂` is recoverable and the inverse exists.  So the sharp form
  of the result is

      distributivity holds (as an iso) exactly on PRECISE arguments,

  and `⌈ r ⌉` -- pinned to a single element by construction -- is the
  motivating instance, giving

      distrib⌈⌉ : ⌈ r ⌉ ⊗× (B ⊗₊ C) ⊢ (⌈ r ⌉ ⊗× B) ⊗₊ (⌈ r ⌉ ⊗× C)

  with an inverse.  Note this is precisely the `□`-modal fragment as
  the rest of this development uses it: `□` is built from
  representables, and representables are precise.  The framework
  expresses the STATEMENT cleanly; see the report for which parts of
  the proof it made awkward.

  ------------------------------------------------------------------
  Everything in this file below `distrib` is PHASE 1: these terms match
  on splittings and on the carrier, and they are the primitives a
  phase-2 program would compose.  `distrib` cannot be a phase-2 term:
  building the splitting `i·p + i·q = n` of the result IS the ring
  axiom, and no combinator of `RulesF` supplies it.  That is the honest
  reading of "distributivity is extra structure on a promodel".
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Ring.Distributivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Equations

open import TheoryGrammar.Instances.Ring.Base public

-- ==================================================================
-- THE LAX DISTRIBUTIVITY MAP.  Phase-1 primitive: it constructs the
-- additive splitting `i·p + i·q = n` out of the ring axiom.
-- ==================================================================

private
  distribBody : (A B C : Gr) (n i j : ℕ) (e : i · j Eq.≡ n)
                (a : A i) (p q : ℕ) (s : SplitAdd p q j) (b : B p) (c : C q)
              → ((A ⊗× B) ⊗₊ (A ⊗× C)) n
  distribBody A B C n i j e a p q s b c =
      (i · p , i · q , sp) , λ { true  → ⊗×-mk Eq.refl a b
                               ; false → ⊗×-mk Eq.refl a c }
                                       -- ^^^ `a` used TWICE: the diagonal
    where
      -- the ring axiom, and nothing else
      eqn : i · p + i · q ≡ n
      eqn = ·-distribˡ i p q ∙ cong (i ·_) (splitAdd≡ s) ∙ Eq.eqToPath e

      sp : SplitAdd (i · p) (i · q) n
      sp = subst (SplitAdd (i · p) (i · q)) eqn (splitAllAdd (i · p) (i · q))

distrib : (A B C : Gr) → (A ⊗× (B ⊗₊ C)) ⊢ ((A ⊗× B) ⊗₊ (A ⊗× C))
distrib A B C n ((i , j , e) , h) =
  distribBody A B C n i j e (h true)
              (h false .fst .fst) (h false .fst .snd .fst)
              (h false .fst .snd .snd)
              (h false .snd true) (h false .snd false)

-- ==================================================================
-- PRECISE GRAMMARS: those that pin their index.
--
-- This is the separation-logic notion of precision, and the internal
-- form of "subterminal".  It is what the INVERSE needs; the forward
-- map above needs nothing.
-- ==================================================================

record Precise (A : Gr) : Type₀ where
  field
    pin    : {i j : ℕ} → A i → A j → i ≡ j
    single : (i : ℕ) → isProp (A i)

open Precise public

-- Representables are precise: `⌈ r ⌉ i = (i Eq.≡ r)` has at most one
-- inhabited index and at most one inhabitant, because ℕ is a set.
⌈⌉Precise : (r : ℕ) → Precise ⌈ r ⌉
⌈⌉Precise r .pin Eq.refl Eq.refl = refl
⌈⌉Precise r .single i =
  subst isProp (Eq.PathPathEq {x = i} {y = r}) (isSetℕ i r)

-- ==================================================================
-- THE INVERSE, on a precise argument.
-- ==================================================================

private
  distribInvBody : (A B C : Gr) (pr : Precise A) (n u v : ℕ)
                   (t : SplitAdd u v n)
                   (i₁ p : ℕ) (e₁ : i₁ · p Eq.≡ u) (a₁ : A i₁) (b : B p)
                   (i₂ q : ℕ) (e₂ : i₂ · q Eq.≡ v) (a₂ : A i₂) (c : C q)
                 → (A ⊗× (B ⊗₊ C)) n
  distribInvBody A B C pr n u v t i₁ p e₁ a₁ b i₂ q e₂ a₂ c =
      (i₁ , p + q , Eq.pathToEq path)
    , λ { true  → a₁
        ; false → ⊗₊-mk (splitAllAdd p q) b c }
    where
      -- the two copies of A are at the SAME index, because A is precise
      same : i₁ ≡ i₂
      same = pin pr a₁ a₂

      path : i₁ · (p + q) ≡ n
      path = sym (·-distribˡ i₁ p q)
           ∙ cong₂ _+_ (Eq.eqToPath e₁)
                       (cong (_· q) same ∙ Eq.eqToPath e₂)
           ∙ splitAdd≡ t

distribInv : (A B C : Gr) → Precise A
           → ((A ⊗× B) ⊗₊ (A ⊗× C)) ⊢ (A ⊗× (B ⊗₊ C))
distribInv A B C pr n ((u , v , t) , g) =
  distribInvBody A B C pr n u v t
    (g true .fst .fst) (g true .fst .snd .fst) (g true .fst .snd .snd)
    (g true .snd true) (g true .snd false)
    (g false .fst .fst) (g false .fst .snd .fst) (g false .fst .snd .snd)
    (g false .snd true) (g false .snd false)

-- ==================================================================
-- THE HEADLINE, as an Iso.
--
-- HOLES.  Both round trips are true and both are stated; neither is
-- closed.  What they need is that the three proof-carrying components
-- of a splitting are propositional -- `SplitAdd u v n` is a prop by
-- induction, `Eq._≡_` on ℕ is a prop because ℕ is a set, and the
-- payloads agree by `single` -- assembled through a `ΣPathP` over an
-- index that itself moves (`u ≡ i₁ · p`).  That is a transport
-- bookkeeping problem, not a mathematical one, and it is exactly the
-- bookkeeping the internal language was supposed to remove; see the
-- report.
-- ==================================================================

-- The three propositional components, and Bool's missing η.  Every
-- splitting in this file is DATA plus a proof, and it is only the proof
-- components that have to be identified -- which is the `Fibered` design
-- paying off: had `Split` carried its equation, these would be paths in
-- the data as well.
private
  -- `isProp (SplitAdd i j n)` CANNOT be matched out directly: the `zl`
  -- clause needs to eliminate the reflexive equation `j = j`, which is
  -- K.  Route it through the equation instead -- `SplitAdd i j n` is the
  -- graph of `+`, hence equivalent to `i + j ≡ n`, which is a prop
  -- because ℕ is a set.  The canonical splitting transports to any other
  -- along its own witness:
  splitAddCanon : {p q w : ℕ} (s : SplitAdd p q w)
                → PathP (λ κ → SplitAdd p q (splitAdd≡ s κ)) (splitAllAdd p q) s
  splitAddCanon zl     = refl
  splitAddCanon (sl s) = λ κ → sl (splitAddCanon s κ)

  fromEq : {i j n : ℕ} → i + j ≡ n → SplitAdd i j n
  fromEq {i} {j} p = subst (SplitAdd i j) p (splitAllAdd i j)

  fromToEq : {i j n : ℕ} (s : SplitAdd i j n) → fromEq (splitAdd≡ s) ≡ s
  fromToEq s = fromPathP (splitAddCanon s)

  isPropSplitAdd : {i j n : ℕ} → isProp (SplitAdd i j n)
  isPropSplitAdd s t =
      sym (fromToEq s)
    ∙ cong fromEq (isSetℕ _ _ (splitAdd≡ s) (splitAdd≡ t))
    ∙ fromToEq t

  isPropEqℕ : {x y : ℕ} → isProp (x Eq.≡ y)
  isPropEqℕ {x} {y} = subst isProp (Eq.PathPathEq {x = x} {y = y}) (isSetℕ x y)

  -- ON THE PAYLOAD PATHS.  `Bool` has no η, so a payload rebuilt
  -- slotwise is only PROPOSITIONALLY the one it came from -- the tax
  -- CLAUDE.md records, and the only reason these round trips are not
  -- `refl`.  It must be discharged INLINE at each use: extended lambdas
  -- are identified NOMINALLY, so a general `boolη`-style lemma produces
  -- a different term from the one `⊗×-mk` built and the two do not
  -- reduce against each other at a variable.
  --
  -- `funExt` escapes this, and note it is already the PathP form in
  -- `Cubical.Foundations.Prelude` -- it takes `(x : A) → PathP (B x) …`
  -- -- so it serves the moving-index slots too.  What makes it work is
  -- that the clause-list is checked against the EXPECTED type, which
  -- splits on the constructors, where both endpoints do reduce.

distrib-Iso : (A B C : Gr) (pr : Precise A) (n : ℕ)
            → Iso ((A ⊗× (B ⊗₊ C)) n) (((A ⊗× B) ⊗₊ (A ⊗× C)) n)
distrib-Iso A B C pr n .Iso.fun = distrib A B C n
distrib-Iso A B C pr n .Iso.inv = distribInv A B C pr n

-- distrib ∘ distribInv ≡ id.  The index moves in three places: the two
-- outer factors (`i₁·p ≡ u`, `i₁·q ≡ v`) and, in the second slot, the
-- A-index itself (`i₁ ≡ i₂`) -- which is exactly where `Precise` is
-- consumed, once for the index (`pin`) and once for the payload
-- (`single`).
distrib-Iso A B C pr n .Iso.sec ((u , v , t) , gg) =
  ΣPathP ( ΣPathP (up , ΣPathP (vp , isProp→PathP (λ _ → isPropSplitAdd) _ t))
         , funExt (λ { true → trueP ; false → falseP }) )
  where
    i₁ = gg true .fst .fst   ; p = gg true .fst .snd .fst
    e₁ = gg true .fst .snd .snd
    a₁ = gg true .snd true   ; b = gg true .snd false
    i₂ = gg false .fst .fst  ; q = gg false .fst .snd .fst
    e₂ = gg false .fst .snd .snd
    a₂ = gg false .snd true  ; c = gg false .snd false

    same : i₁ ≡ i₂
    same = pin pr a₁ a₂

    up : i₁ · p ≡ u
    up = Eq.eqToPath e₁

    vp : i₁ · q ≡ v
    vp = cong (_· q) same ∙ Eq.eqToPath e₂

    trueP : PathP (λ κ → (A ⊗× B) (up κ)) (⊗×-mk Eq.refl a₁ b) (gg true)
    trueP = ΣPathP ( ΣPathP (refl , ΣPathP (refl , isProp→PathP (λ _ → isPropEqℕ) _ e₁))
                   , funExt (λ { true → refl ; false → refl }) )

    falseP : PathP (λ κ → (A ⊗× C) (vp κ)) (⊗×-mk Eq.refl a₁ c) (gg false)
    falseP = ΣPathP ( ΣPathP (same , ΣPathP (refl , isProp→PathP (λ _ → isPropEqℕ) _ e₂))
                    , funExt (λ { true  → isProp→PathP (λ κ → single pr (same κ)) a₁ a₂
                                 ; false → refl }) )

-- distribInv ∘ distrib ≡ id.  Only ONE index moves here -- `p + q ≡ j`,
-- the cofactor -- because the diagonal `distrib` introduces is undone by
-- reading both copies off the same slot.
distrib-Iso A B C pr n .Iso.ret ((i , j , e) , h) =
  ΣPathP ( ΣPathP (refl , ΣPathP (jp , isProp→PathP (λ _ → isPropEqℕ) _ e))
         , funExt (λ { true → refl ; false → falseP }) )
  where
    p = h false .fst .fst  ; q = h false .fst .snd .fst
    s = h false .fst .snd .snd

    jp : p + q ≡ j
    jp = splitAdd≡ s

    falseP : PathP (λ κ → (B ⊗₊ C) (jp κ))
                   (⊗₊-mk (splitAllAdd p q) (h false .snd true) (h false .snd false))
                   (h false)
    falseP = ΣPathP ( ΣPathP (refl , ΣPathP (refl , isProp→PathP (λ _ → isPropSplitAdd) _ s))
                    , funExt (λ { true → refl ; false → refl }) )

-- ==================================================================
-- THE REPRESENTABLE CASE.  `⌈ r ⌉` is precise, so distributivity is an
-- isomorphism there -- distributivity holds on the □-modal fragment.
-- ==================================================================

distrib⌈⌉ : (r : ℕ) (B C : Gr)
          → (⌈ r ⌉ ⊗× (B ⊗₊ C)) ⊢ ((⌈ r ⌉ ⊗× B) ⊗₊ (⌈ r ⌉ ⊗× C))
distrib⌈⌉ r B C = distrib ⌈ r ⌉ B C

distrib⌈⌉⁻ : (r : ℕ) (B C : Gr)
           → ((⌈ r ⌉ ⊗× B) ⊗₊ (⌈ r ⌉ ⊗× C)) ⊢ (⌈ r ⌉ ⊗× (B ⊗₊ C))
distrib⌈⌉⁻ r B C = distribInv ⌈ r ⌉ B C (⌈⌉Precise r)

distrib⌈⌉-Iso : (r : ℕ) (B C : Gr) (n : ℕ)
              → Iso ((⌈ r ⌉ ⊗× (B ⊗₊ C)) n) (((⌈ r ⌉ ⊗× B) ⊗₊ (⌈ r ⌉ ⊗× C)) n)
distrib⌈⌉-Iso r B C = distrib-Iso ⌈ r ⌉ B C (⌈⌉Precise r)

-- ==================================================================
-- AND THE PRECISION HYPOTHESIS IS NECESSARY.  A proved refutation.
--
-- Take A = ⊤ (maximally imprecise: every index inhabited),
-- B = C = ⌈1⌉, and look at n = 3.
--
--   RIGHT side:  3 = 1 + 2,  1 = 1·1,  2 = 2·1.   INHABITED.
--   LEFT side:   B ⊗₊ C pins its index to 1 + 1 = 2, so the outer
--                Dirichlet splitting must solve i · 2 = 3.   EMPTY.
--
-- The two `⊤`-slots on the right sit at indices 1 and 2 -- the two
-- copies of A that a general A cannot be forced to agree on.  So
-- `distrib` is genuinely lax: there is not merely no canonical
-- inverse, there is NO isomorphism at all.
-- ==================================================================

private
  ·2≢1 : (i : ℕ) → i · 2 ≡ 1 → ⊥
  ·2≢1 zero    p = znots p
  ·2≢1 (suc i) p = snotz (injSuc p)

  ·2≢3 : (i : ℕ) → i · 2 ≡ 3 → ⊥
  ·2≢3 zero    p = znots p
  ·2≢3 (suc i) p = ·2≢1 i (injSuc (injSuc p))

  -- `⌈1⌉ ⊗₊ ⌈1⌉` is supported at 2 only, so `i · j = 3` is unsolvable
  no3 : (i j p q : ℕ) → p Eq.≡ 1 → q Eq.≡ 1
      → SplitAdd p q j → i · j Eq.≡ 3 → ⊥
  no3 i j p q Eq.refl Eq.refl (sl zl) e = ·2≢3 i (Eq.eqToPath e)

lhs-empty : (⊤G ⊗× (⌈ 1 ⌉ ⊗₊ ⌈ 1 ⌉)) 3 → ⊥
lhs-empty ((i , j , e) , h) =
  no3 i j (h false .fst .fst) (h false .fst .snd .fst)
      (h false .snd true) (h false .snd false)
      (h false .fst .snd .snd) e

rhs-pt : ((⊤G ⊗× ⌈ 1 ⌉) ⊗₊ (⊤G ⊗× ⌈ 1 ⌉)) 3
rhs-pt =
    (1 , 2 , sl zl)
  , λ { true  → (1 , 1 , Eq.refl) , λ { true → tt ; false → Eq.refl }
      ; false → (2 , 1 , Eq.refl) , λ { true → tt ; false → Eq.refl } }

-- THEOREM.  Distributivity is not invertible without a hypothesis on A.
distrib-not-iso :
  Iso ((⊤G ⊗× (⌈ 1 ⌉ ⊗₊ ⌈ 1 ⌉)) 3) (((⊤G ⊗× ⌈ 1 ⌉) ⊗₊ (⊤G ⊗× ⌈ 1 ⌉)) 3) → ⊥
distrib-not-iso is = lhs-empty (is .Iso.inv rhs-pt)

-- ==================================================================
-- POSITIVE CONTROL: a LINEAR equation of the same theory DOES lift,
-- by `eqn→Iso`, with no work at all.
--
-- Commutativity `x · y = y · x` uses each variable once on each side,
-- so the flattening theorem applies and the two composite connectives
-- are isomorphic.  Contrast distributivity above, which needed a
-- hand-built map and a precision hypothesis to invert.  Note these are
-- the connectives of the EQUATIONAL presentation (`⟪_⟫` = `⊗ᶠ` over
-- the model `⌊ natPoint ⌋`), not `⊗ˢ`; `⊗ᶠ≡⊗` relates the two.
-- ==================================================================

private
  Two : Type₀
  Two = Bool

  mulTm : Tm ringSig Two (λ _ → tt) tt
  mulTm = node mulOp var

  mulTm' : Tm ringSig Two (λ _ → tt) tt
  mulTm' = node mulOp (λ b → var (not b))

  comm-sat : (ρ : Val ⌊ natPoint ⌋ {V = Two} (λ _ → tt))
           → eval ⌊ natPoint ⌋ ρ mulTm Eq.≡ eval ⌊ natPoint ⌋ ρ mulTm'
  comm-sat ρ = Eq.pathToEq (·-comm (ρ true) (ρ false))

  ⊗×-comm-Iso : (A : Two → Gr) (n : ℕ)
              → Iso (⟪_⟫ ⌊ natPoint ⌋ mulTm' A n) (⟪_⟫ ⌊ natPoint ⌋ mulTm A n)
  ⊗×-comm-Iso A = eqn→Iso ⌊ natPoint ⌋ mulTm mulTm' comm-sat
