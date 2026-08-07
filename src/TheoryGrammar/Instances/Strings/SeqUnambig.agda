{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Levi's lemma, and sequential unambiguity on top of it.

   Levi -- equidivisibility -- is the hypothesis `PORTING.md` names as
   the blocker for `SequentialUnambiguity` and `Greedy`, and the one
   thing the generic layer cannot supply (it is false for bags).  Over
   the INDUCTIVE `Split3` it is a three-clause double recursion with no
   arithmetic, no `split++`, and no length induction.  That is the same
   payoff the derivative got, in a second place.

   On top of it, `First` and `FollowLast` are recast as DERIVATIVES
   rather than as subsets of the alphabet:

       c ∉First A       is    δ_c A ⊢ ⊥
       c ∉FollowLast A  is    δ_c (A ⊗ ⊤ ∩ …) ⊢ ⊥

   which removes the powerset machinery the original needed -- they are
   grammars, so they are compared with `⊢` like everything else. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.SeqUnambig
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as E using (⊥; ⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable using (No)

open import TheoryGrammar.Instances.Strings.RegExp Char decChar public

-- ==================================================================
-- LEVI'S LEMMA.
--
-- Two splittings of one word are comparable: one cut is no later than
-- the other, and the middle piece `t` is the difference.
-- ==================================================================

-- "sp cuts no later than sp'": u₂ = u₁ ++ t and v₁ = t ++ v₂
Refines : String → String → String → String → Type₀
Refines u₁ v₁ u₂ v₂ = Σ[ t ∈ String ] (Split3 u₁ t u₂ × Split3 t v₂ v₁)

levi : ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
     → Refines u₁ v₁ u₂ v₂ ⊎ Refines u₂ v₂ u₁ v₁
levi nil       sp'        = inl (_ , nil , sp')
levi (cons sp) nil        = inr (_ , nil , cons sp)
levi (cons sp) (cons sp') = go (levi sp sp')
  where go : _ → _
        go (inl (t , p , q)) = inl (t , cons p , q)
        go (inr (t , p , q)) = inr (t , cons p , q)

-- ==================================================================
-- FIRST and FOLLOWLAST, as derivatives rather than as subsets.
--
-- The original carried `c ∉First A` as an element of a powerset over
-- the alphabet, with `Powerset.More` and truncation to keep it a
-- proposition.  None of that is needed: "A cannot start with c" IS
-- "δ_c A is empty", and emptiness of a grammar is `⊢ ⊥`.
-- ==================================================================

∉First : Char → Gr → Type₀
∉First c A = Derivᶜ.δ c A ⊢ ⊥G

-- "no complete parse of A extends, by c, to another parse of A"
∉FollowLast : Char → Gr → Type₀
∉FollowLast c A = ∀ {u v w} → A u → Split3 u (c ∷ v) w → A w → ⊥*

_⊛_ : Gr → Gr → Type₀
A ⊛ B = (c : Char) → ∉FollowLast c A ⊎ ∉First c B

infix 10 _⊛_

private
  split3Nil : ∀ {u w} → Split3 u [] w → u Eq.≡ w
  split3Nil nil     = Eq.refl
  split3Nil (cons s) = go (split3Nil s)
    where go : _ → _
          go Eq.refl = Eq.refl

-- ==================================================================
-- THE THEOREM.  Under `A ⊛ B` a word has AT MOST ONE splitting
-- compatible with A and B -- so `A ⊗ B` is read deterministically,
-- and the `length w + 1` cuts collapse to one.
--
-- The proof is Levi plus one case analysis: if the two cuts differ,
-- the middle piece starts with some `c`, and then `c` both follows a
-- complete A-parse and starts a B-parse -- which is exactly what `⊛`
-- forbids.
-- ==================================================================

sameSplit : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂ → u₁ Eq.≡ u₂
sameSplit {A} {B} su sp sp' a₁ b₁ a₂ b₂ = go (levi sp sp')
  where
    go : _ → _
    -- the cuts coincide
    go (inl (_ , p , nil))  = split3Nil p
    go (inr (_ , p , nil))  = flip (split3Nil p)
      where flip : _ → _
            flip Eq.refl = Eq.refl
    -- they differ, by a middle piece starting with c' -- impossible
    go (inl (_ , p , cons {c = c'} q')) = clash (su c')
      where clash : _ → _
            clash (inl nf)  = E.rec (lower (nf a₁ p a₂))
            clash (inr nfi) = E.rec (lower (nfi _ b₁))
    go (inr (_ , p , cons {c = c'} q')) = clash (su c')
      where clash : _ → _
            clash (inl nf)  = E.rec (lower (nf a₂ p a₁))
            clash (inr nfi) = E.rec (lower (nfi _ b₂))

-- ==================================================================
-- The cheapest source of `⊛`: a literal can never be followed, since
-- a one-character parse has no proper extension that is still a
-- one-character parse.  So `literal a ⊛ B` for EVERY B.
-- ==================================================================

-- NOTE: this cannot be done by matching the splitting.  `Char` is not
-- assumed discrete, so unifying `c ∷ w` with `a ∷ []` would need K,
-- which cubical disables.  Counting is the way through -- and the
-- count is the same `Split3`-recursion, so nothing is lost.
split3Len : ∀ {u v w} → Split3 u v w → length u + length v Eq.≡ length w
split3Len nil      = Eq.refl
split3Len (cons s) = Eq.ap suc (split3Len s)

litNoFollow : (a c : Char) → ∉FollowLast c (literal a)
litNoFollow a c {v = v} Eq.refl sp Eq.refl = go (split3Len sp)
  where go : (suc (suc (length v)) Eq.≡ 1) → ⊥*
        go ()

lit⊛ : (a : Char) (B : Gr) → literal a ⊛ B
lit⊛ a B c = inl (litNoFollow a c)

-- The cut determines the remainder, so `sameSplit` upgrades to both
-- components.  Matching the two splittings against each other does NOT
-- work -- the two `cons`es contribute independent head variables and
-- the unifier is left with a reflexive equation on `Char`, which needs
-- K.  Going through concatenation avoids ever unifying two heads.
split3App : ∀ {u v w} → Split3 u v w → w Eq.≡ (u ++ v)
split3App nil      = Eq.refl
split3App (cons s) = Eq.ap (λ z → _ ∷ z) (split3App s)

-- ... and for the same reason `cons` injectivity has to be `ap tail`
-- rather than a match: `ap` never unifies the heads at all.
tl : String → String
tl []       = []
tl (_ ∷ xs) = xs

++cancelL : (u : String) {v v' : String} → (u ++ v) Eq.≡ (u ++ v') → v Eq.≡ v'
++cancelL []      e = e
++cancelL (c ∷ u) e = ++cancelL u (Eq.ap tl e)

split3Fun : ∀ {u v v' w} → Split3 u v w → Split3 u v' w → v Eq.≡ v'
split3Fun {u} {v} {v'} s s' = go (split3App s) s'
  where go : ∀ {w'} → w' Eq.≡ (u ++ v) → Split3 u v' w' → v Eq.≡ v'
        go Eq.refl s'' = ++cancelL u (split3App s'')

sameParts : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂
          → (u₁ Eq.≡ u₂) × (v₁ Eq.≡ v₂)
sameParts su sp sp' a₁ b₁ a₂ b₂ = go (sameSplit su sp sp' a₁ b₁ a₂ b₂)
  where go : _ → _
        go Eq.refl = Eq.refl , split3Fun sp sp'

-- ==================================================================
-- WHY THIS IS NOT `DecReadable`.
--
-- `Decidable/Rule.fromUnique` consumes `DecReadable`, whose `splitProp`
-- says the PROMODEL has at most one decomposition.  That is flatly
-- false for strings -- `w` has `length w + 1` of them -- and no amount
-- of sequential unambiguity changes it.
--
-- What `⊛` buys is strictly weaker and strictly more useful: at most
-- one decomposition COMPATIBLE WITH A AND B.  Uniqueness is relative to
-- the grammars, not a property of the promodel, and the existing
-- interface has no place to say that.  Recording it here rather than
-- bending `DecReadable` to fit: the honest fix is a grammar-relative
-- unique-readability constructor, which is a change to
-- `Decidable/Tensor.agda` and should be made deliberately.
-- ==================================================================

-- ==================================================================
-- `Split3` IS A PROPOSITION -- the parts pin the witness.
--
-- This is `PartsFaithful` (TheoryGrammar.Fibered) for strings, and it
-- was the thing three separate results were waiting on: unambiguity of
-- `A ⊗ B`, `Free` for the string scan, and the K-failures earlier in
-- this file.
--
-- TWO THINGS ABOUT THE SHAPE OF IT.
--
-- First, the hypothesis is an ARGUMENT, not a module parameter.  I had
-- been proposing to thread `isSet Char` through the whole Strings
-- chain; that is unnecessary -- only these lemmas want it, so only
-- these lemmas take it.
--
-- Second, and this is why it works at all: the retraction needs NO set
-- hypothesis.  `Split3 u v w` retracts onto `w ≡ u ++ v` outright.  The
-- set-ness is used only to know the TARGET is a proposition, which is
-- `HLevels.⌈⌉-isProp`'s observation one level down -- a path in a set.
-- ==================================================================

split3Of : ∀ {u v w} → w Eq.≡ (u ++ v) → Split3 u v w
split3Of {u = u} {v = v} Eq.refl = splitAll u v

private
  -- `split3Of` commutes with consing, which is the only step the
  -- induction needs
  split3Of-∷ : ∀ {c u v w} (e : w Eq.≡ (u ++ v))
             → split3Of {c ∷ u} {v} (Eq.ap (λ z → c ∷ z) e) ≡ cons (split3Of e)
  split3Of-∷ Eq.refl = refl

  split3-retract : ∀ {u v w} (s : Split3 u v w) → split3Of (split3App s) ≡ s
  split3-retract nil      = refl
  split3-retract (cons t) = split3Of-∷ (split3App t) ∙ cong cons (split3-retract t)

  propEqStr : isSet String → {x y : String} → isProp (x Eq.≡ y)
  propEqStr ss {x} {y} = subst isProp Eq.PathPathEq (ss x y)

split3IsProp : isSet String → ∀ {u v w} → isProp (Split3 u v w)
split3IsProp ss =
  isOfHLevelRetract 1 split3App split3Of split3-retract (propEqStr ss)

-- ... and hence the general property, discharged.  `PartsFaithful` says
-- a decomposition is determined by its parts; for strings the parts
-- give the two components and `split3IsProp` gives the third.
strPartsFaithful : isSet String → PartsFaithful strFib appop
strPartsFaithful ss m (u , v , s) (u' , v' , s') e =
  ΣPathP (eu , ΣPathP (ev , isProp→PathP (λ _ → split3IsProp ss) s s'))
  where
    eu : u ≡ u'
    eu = funExt⁻ e true
    ev : v ≡ v'
    ev = funExt⁻ e false

-- ==================================================================
-- UNAMBIGUITY OF THE TENSOR, INTERNALLY.
--
-- `isProp ((A ⊗ B) w)` is an EXTERNAL statement -- a claim about the
-- semantic type.  The internal content is a TERM:
--
--     ⊗-align : (A ⊗ B) & (A ⊗ B)  ⊢  (A & A) ⊗ (B & B)
--
-- "two parses of a tensor decompose the same way, so they pair up
-- slot-wise".  That is exactly the converse of `BaseChange.Σᴿ-&`,
-- which holds unconditionally in the other direction -- Σ always
-- distributes OUT of a conjunction, and distributing back IN is
-- precisely the statement that the accessibility structure is
-- determined.  So the internal form of "the tensor is unambiguous" is
-- not a proposition at all; it is the missing half of a distributivity.
--
-- Both hypotheses are used, and for different halves: `⊛` (via `levi`
-- and `sameParts`) gives that the PARTS agree, and `split3IsProp` that
-- the WITNESS does.  That is the two-property split `PartsFaithful`
-- names, appearing here as two steps of one proof.
-- ==================================================================

module _ (ss : isSet String) {A B : Gr} (su : A ⊛ B) where

  private
    spEq : (w : String) (sp sp' : MonSplit appop w)
         → A (MonParts appop w sp true)  → B (MonParts appop w sp false)
         → A (MonParts appop w sp' true) → B (MonParts appop w sp' false)
         → sp ≡ sp'
    spEq w (u , v , s) (u' , v' , s') a b a' b' =
      strPartsFaithful ss w (u , v , s) (u' , v' , s')
        (funExt λ { true  → Eq.eqToPath (sameParts su s s' a b a' b' .fst)
                  ; false → Eq.eqToPath (sameParts su s s' a b a' b' .snd) })

  ⊗-align : ((A ⊗' B) & (A ⊗' B)) ⊢ ((A & A) ⊗' (B & B))
  ⊗-align w ((sp , h) , (sp' , h')) =
    sp , λ { true  → h true  , subst (λ s → A (MonParts appop w s true))
                                     (sym eq) (h' true)
           ; false → h false , subst (λ s → B (MonParts appop w s false))
                                     (sym eq) (h' false) }
    where eq : sp ≡ sp'
          eq = spEq w sp sp' (h true) (h false) (h' true) (h' false)

  -- The external statement, for comparison.  Note where the work is:
  -- `eq` -- the alignment -- is the whole content, and the two
  -- propositions only collapse the paired payloads afterwards.
  ⊗-unambiguous : ((w : String) → isProp (A w))
                → ((w : String) → isProp (B w))
                → (w : String) → isProp ((A ⊗' B) w)
  ⊗-unambiguous pa pb w (sp , h) (sp' , h') =
    ΣPathP (eq , isProp→PathP
                   (λ _ → isPropΠ λ { true → pa _ ; false → pb _ }) h h')
    where eq : sp ≡ sp'
          eq = spEq w sp sp' (h true) (h false) (h' true) (h' false)
