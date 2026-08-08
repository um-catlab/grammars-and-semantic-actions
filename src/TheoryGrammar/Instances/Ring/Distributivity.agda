{- DISTRIBUTIVITY IS A LAX MAP, AND IT IS INVERTIBLE EXACTLY ON PRECISE
   ARGUMENTS. -}
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

-- THE LAX DISTRIBUTIVITY MAP.  Phase-1 primitive: it constructs the
-- additive splitting `i·p + i·q = n` out of the ring axiom.

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

-- PRIMITIVE (phase 1): the nested `⊗ˢ` payload it rebuilds is a HAND-
-- ROLLED `Σ`, not a composite of connectives, so there is nothing for
-- `⊗ˢ-E`/`&-E` to act on and the projection has to be written out.
distrib : (A B C : Gr) → (A ⊗× (B ⊗₊ C)) ⊢ ((A ⊗× B) ⊗₊ (A ⊗× C))
distrib A B C n ((i , j , e) , h) =
  distribBody A B C n i j e (h true)
              (h false .fst .fst) (h false .fst .snd .fst)
              (h false .fst .snd .snd)
              (h false .snd true) (h false .snd false)

-- PRECISE GRAMMARS: those that pin their index.

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

-- THE INVERSE, on a precise argument.

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

-- PRIMITIVE (phase 1): the nested `⊗ˢ` payload it rebuilds is a HAND-
-- ROLLED `Σ` rather than a composite of connectives, so there is nothing
-- for the elim rules to act on.
distribInv : (A B C : Gr) → Precise A
           → ((A ⊗× B) ⊗₊ (A ⊗× C)) ⊢ (A ⊗× (B ⊗₊ C))
distribInv A B C pr n ((u , v , t) , g) =
  distribInvBody A B C pr n u v t
    (g true .fst .fst) (g true .fst .snd .fst) (g true .fst .snd .snd)
    (g true .snd true) (g true .snd false)
    (g false .fst .fst) (g false .fst .snd .fst) (g false .fst .snd .snd)
    (g false .snd true) (g false .snd false)

-- THE HEADLINE, as an Iso. HOLES.

-- The three propositional components, and Bool's missing η.
private
  -- `isProp (SplitAdd i j n)` CANNOT be matched out directly: the `zl`
  -- clause needs to eliminate the reflexive equation `j = j`, which is K.
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

  -- ON THE PAYLOAD PATHS. `Bool` has no η, so a payload rebuilt slotwise
  -- is only PROPOSITIONALLY the one it came from -- the arity-η tax, and
  -- the only reason these round trips are not `refl`.

distrib-Iso : (A B C : Gr) (pr : Precise A) (n : ℕ)
            → Iso ((A ⊗× (B ⊗₊ C)) n) (((A ⊗× B) ⊗₊ (A ⊗× C)) n)
distrib-Iso A B C pr n .Iso.fun = distrib A B C n
distrib-Iso A B C pr n .Iso.inv = distribInv A B C pr n

-- distrib ∘ distribInv ≡ id. The index moves in three places: the two
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

-- THE REPRESENTABLE CASE.  `⌈ r ⌉` is precise, so distributivity is an
-- isomorphism there -- distributivity holds on the □-modal fragment.

distrib⌈⌉ : (r : ℕ) (B C : Gr)
          → (⌈ r ⌉ ⊗× (B ⊗₊ C)) ⊢ ((⌈ r ⌉ ⊗× B) ⊗₊ (⌈ r ⌉ ⊗× C))
distrib⌈⌉ r B C = distrib ⌈ r ⌉ B C

distrib⌈⌉⁻ : (r : ℕ) (B C : Gr)
           → ((⌈ r ⌉ ⊗× B) ⊗₊ (⌈ r ⌉ ⊗× C)) ⊢ (⌈ r ⌉ ⊗× (B ⊗₊ C))
distrib⌈⌉⁻ r B C = distribInv ⌈ r ⌉ B C (⌈⌉Precise r)

distrib⌈⌉-Iso : (r : ℕ) (B C : Gr) (n : ℕ)
              → Iso ((⌈ r ⌉ ⊗× (B ⊗₊ C)) n) (((⌈ r ⌉ ⊗× B) ⊗₊ (⌈ r ⌉ ⊗× C)) n)
distrib⌈⌉-Iso r B C = distrib-Iso ⌈ r ⌉ B C (⌈⌉Precise r)

-- AND THE PRECISION HYPOTHESIS IS NECESSARY. A proved refutation.

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

-- POSITIVE CONTROL: a LINEAR equation of the same theory DOES lift, by
-- `eqn→Iso`, with no work at all.

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
