{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  LENGTH IS A DISCRETE CONDUCHÉ FUNCTOR.  The positive example that
  `TheoryGrammar.ChangeOfTheory` was missing.

  ------------------------------------------------------------------
  THE CLAIM
  ------------------------------------------------------------------

  `ChangeOfTheory` proves that a `ModelHom h : M → N` reinterprets the
  ADDITIVE fragment definitionally, and the MULTIPLICATIVE fragment only
  laxly -- `pull⊗` always exists, `pull⊗⁻` exists exactly when h
  REFLECTS SPLITTINGS.  Its header then gives a NEGATIVE example:

      abelianisation  List Char → Multiset Char

  is a monoid homomorphism, but {a,b} splits as {a}|{b} AND as {b}|{a}
  while "ab" splits only as "a"|"b".  So string grammars do not
  reinterpret as multiset grammars multiplicatively.

  This file supplies the missing POSITIVE example:

      length : List Char → ℕ

  is a monoid homomorphism which DOES reflect splittings.  Given w and a
  decomposition i + j = |w| of its length, there is a decomposition
  u ++ v = w of w itself with |u| = i and |v| = j -- namely the cut of w
  at position i -- and it is UNIQUE.  Hence `pull⊗⁻` exists and the
  multiplicative fragment transports as an EQUIVALENCE.

  ------------------------------------------------------------------
  WHY THE TWO EXAMPLES ARE THE SAME PICTURE
  ------------------------------------------------------------------

  Both maps forget something. Abelianisation forgets ORDER; `length`
  forgets IDENTITY of letters. The difference is what happens to the
  fibres of a factorisation:

      abelianisation:  a factorisation downstairs has MANY lifts
                       ({a,b} = {a}|{b} lifts to "ab" and to "ba")
      length:          a factorisation downstairs has EXACTLY ONE lift
                       (3 = 1+2 lifts, over "abc", only to "a"|"bc")

  "Discrete Conduché" is precisely the second condition -- unique lifting
  of factorisations -- and it is the exact boundary at which
  reinterpretation stops being lax.  Existence gives the map `pull⊗⁻`;
  uniqueness (`splitUnique` below) is what makes the pair inverse.

  The reason `length` is Conduché and abelianisation is not, stated
  monoid-theoretically: `length` is the unique monoid map to the free
  monoid on ONE generator induced by collapsing the alphabet, and
  collapsing generators is a map of FREE monoids that preserves the
  length function -- so a factorisation of the image is determined by a
  cut position, and cut positions transfer.  Abelianisation leaves the
  free world entirely.

  ------------------------------------------------------------------
  THE PAYOFF
  ------------------------------------------------------------------

  A ℕ-graded type is a graded set, i.e. a formal power series with type
  coefficients (see `Instances/Nat/Base.agda`), and an isomorphism of
  ℕ-graded types is a generating-function identity WITH ITS BIJECTION.
  Composing with `pull` and `pull⊗⁻`, every such identity becomes an
  isomorphism of string grammars for free:

      A(x) ≅ B(x)·C(x)   over ℕ
      ----------------------------------------
      pull A ≅ pull B ⊗ pull C   over List Char

  and `pull` is by definition "reindex by length", so `pull A w` is
  "A at |w|".  That is exactly the passage from "counts of Dyck words of
  each length" to "the grammar of Dyck words" -- see `Species.agda`.

  ------------------------------------------------------------------
  A DEFECT, RECORDED
  ------------------------------------------------------------------

  `Strings/Base.agda`, `Bags/Base.agda` and `Nat/Base.agda` each declare
  their OWN `data MonOp` with the same two constructors.  They are
  definitionally distinct types, so `ModelHom strModel natModel` cannot
  even be STATED using `Nat/Base`'s signature.  This file therefore
  builds the ℕ-model directly over the STRINGS `monoidSig`, duplicating four
  lines.  The monoid signature wants to be a shared module (say
  `TheoryGrammar.Signatures.Monoid`) that all three instances import.
  See the report accompanying this file.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Length (Char : Type₀) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.ChangeOfTheory

-- The STRING instance, read-only.  Note this brings the string-side
-- `_⊢_`, `⊗ˢ`, `⊗[_]`, `⌈_⌉`, `Gr`, `_⊗'_` into scope UNQUALIFIED; the
-- ℕ side is reached through `module ℕM` below.
open import TheoryGrammar.Instances.Strings.Connectives Char public

-- Qualified: `Nat/Base` exports `MonSplit`, `MonParts`, `Gr` under the
-- same names as the string instance, so only the ℕ promodel and its
-- point are wanted here.
import TheoryGrammar.Instances.Nat.Connectives as N

-- ==================================================================
-- THE TWO MODELS, at one and the same signature.
-- ==================================================================

strModel : Model monoidSig ℓ-zero
strModel = ⌊ strPoint ⌋

-- `⊗[_]` is the MODEL-level convolution (it mentions `op`), so since the
-- `Fibered`/`LaxPoint` split it is no longer exported by `FibNotation` --
-- which is the point: the substrate-level `⊗ˢ` needs only `Split`.  The
-- bridges below relate the two, so they need the model-level one by name.
open Notation strModel using (⊗[_])

-- The ℕ-model of the monoid signature.  This USED to be rebuilt by hand,
-- because `Strings/Base` and `Nat/Base` each declared their own `MonOp`
-- and the two `monoidSig`s were definitionally distinct -- so
-- `ModelHom strModel natModel` could not be stated across them.  With
-- the signature shared in `TheoryGrammar.Theories.Monoid` the duplication
-- is gone: this is literally `Nat/Base`'s promodel with its point.
natModel : Model monoidSig ℓ-zero
natModel = ⌊ N.natPoint ⌋

module ℕM = Notation natModel

-- ℕ-graded types: the power-series side.
NatGr : Type₁
NatGr = ℕM.TheoryTy ℓ-zero tt

-- ==================================================================
-- `length` IS A MONOID HOMOMORPHISM.
-- ==================================================================

-- PRIMITIVE (phase 1): |u ++ v| = |u| + |v|, at `Eq` so that it can be
-- matched on rather than transported along.
lengthApp : (u v : String) → length (u ++ v) Eq.≡ length u + length v
lengthApp []      v = Eq.refl
lengthApp (c ∷ u) v = Eq.ap suc (lengthApp u v)

lengthHom : ModelHom strModel natModel
lengthHom .hom _         = length
lengthHom .homOp nilop f = Eq.refl
lengthHom .homOp appop f = lengthApp (f true) (f false)

-- ==================================================================
-- REFLECTION OF SPLITTINGS.  The mathematical content of the file.
-- ==================================================================

-- PRIMITIVE (phase 1): THE CUT.  Given a decomposition i + j = |w| of
-- the LENGTH, produce the decomposition of `w` itself.  This is
-- `splitAt i`, written so that the two length equations come out of the
-- same recursion rather than being proved afterwards.
cut : (i j : ℕ) (w : String)
    → i + j Eq.≡ length w
    → Σ[ u ∈ String ] Σ[ v ∈ String ]
        ((u ++ v Eq.≡ w) × (length u Eq.≡ i) × (length v Eq.≡ j))
cut zero    j w       e = [] , w , Eq.refl , Eq.refl , Eq.sym e
cut (suc i) j []      ()
cut (suc i) j (c ∷ w) e =
  let (u , v , eu , eiu , ejv) = cut i j w (Eq.ap predℕ e)
  in c ∷ u , v , Eq.ap (c ∷_) eu , Eq.ap suc eiu , ejv

-- PRIMITIVE (phase 1): the degenerate case, for the nullary operation.
zeroLen : (w : String) → 0 Eq.≡ length w → [] Eq.≡ w
zeroLen []      _ = Eq.refl
zeroLen (c ∷ w) ()

open Reinterpret lengthHom public

-- ==================================================================
-- THE THEOREM.
-- ==================================================================

lengthReflects : ReflectsSplit
lengthReflects nilop w n⃗ e = (λ ()) , zeroLen w e , λ ()
lengthReflects appop w n⃗ e =
  let (u , v , eu , eiu , ejv) = cut (n⃗ true) (n⃗ false) w e
  in (λ b → if b then u else v)
   , eu
   , λ { true → eiu ; false → ejv }

-- ==================================================================
-- ... AND THE LIFT IS UNIQUE.  This is the second half of "discrete
-- Conduché", and it is what upgrades `pull⊗` / `pull⊗⁻` from a
-- retraction to an isomorphism.
-- ==================================================================

private
  tail' : String → String
  tail' []      = []
  tail' (_ ∷ w) = w

  head' : Char → String → Char
  head' d []      = d
  head' d (c ∷ _) = c

  consEq : {c c' : Char} {u u' : String}
         → c Eq.≡ c' → u Eq.≡ u' → (c ∷ u) Eq.≡ (c' ∷ u')
  consEq Eq.refl Eq.refl = Eq.refl

-- PRIMITIVE (phase 1): a cut is determined by where it cuts.
splitUnique : (u v u' v' : String)
            → u ++ v Eq.≡ u' ++ v'
            → length u Eq.≡ length u'
            → (u Eq.≡ u') × (v Eq.≡ v')
splitUnique []      v []       v' e el = Eq.refl , e
splitUnique []      v (c ∷ u') v' e ()
splitUnique (c ∷ u) v []       v' e ()
splitUnique (c ∷ u) v (d ∷ u') v' e el =
  let (eu , ev) = splitUnique u v u' v' (Eq.ap tail' e) (Eq.ap predℕ el)
  in consEq (Eq.ap (head' c) e) eu , ev

-- The `appop` instance: two lifts of the same ℕ-splitting agree
-- slotwise.  With `lengthReflects`, this is the discrete Conduché
-- condition in full: the lift EXISTS and its underlying decomposition is
-- UNIQUE.
--
-- Stated honestly: this gives uniqueness of the DATA (`m⃗`), not
-- contractibility of the whole lift type.  The lift also carries proof
-- components in `Eq._≡_` at `String`, and `Eq._≡_` is a proposition only
-- when the carrier is a set -- which needs `Discrete Char`, an
-- assumption this file deliberately does not make.  `pull⊗⁻` never
-- needed it: existence alone builds the map, and uniqueness of `m⃗` is
-- what makes the map canonical rather than a choice.
liftUnique : (w : String) (n⃗ : Bool → ℕ) (m⃗ m⃗' : Bool → String)
           → m⃗  true ++ m⃗  false Eq.≡ w
           → m⃗' true ++ m⃗' false Eq.≡ w
           → ((a : Bool) → length (m⃗  a) Eq.≡ n⃗ a)
           → ((a : Bool) → length (m⃗' a) Eq.≡ n⃗ a)
           → ((a : Bool) → m⃗ a Eq.≡ m⃗' a)
liftUnique w n⃗ m⃗ m⃗' e e' l l' =
  let (et , ef) = splitUnique (m⃗ true) (m⃗ false) (m⃗' true) (m⃗' false)
                    (e Eq.∙ Eq.sym e')
                    (l true Eq.∙ Eq.sym (l' true))
  in λ { true → et ; false → ef }

-- And the same statement about `cut` itself: whatever decomposition of
-- `w` has the prescribed lengths, `cut` already found it.  This is the
-- "unique lifting of factorisations" of the discrete Conduché condition,
-- said about the actual lifting map rather than abstractly.
cut-unique : (i j : ℕ) (w u v : String)
           → u ++ v Eq.≡ w → length u Eq.≡ i → length v Eq.≡ j
           → (e : i + j Eq.≡ length w)
           → (cut i j w e .fst Eq.≡ u) × (cut i j w e .snd .fst Eq.≡ v)
cut-unique i j w u v euv lu lv e =
  let (u' , v' , euv' , lu' , lv') = cut i j w e
  in splitUnique u' v' u v (euv' Eq.∙ Eq.sym euv) (lu' Eq.∙ Eq.sym lu)

-- ==================================================================
-- CROSSING BETWEEN ⊗ˢ AND ⊗[_].
--
-- `Reinterpret` is stated at the MODEL-level ⊗ (the one carrying an
-- equation), while programs are written against the SUBSTRATE-level ⊗ˢ.
-- These two primitives are the translation at strings; they are generic
-- in nothing and belong in `TheoryGrammar.Fibered` upstream, where the
-- general statement is `⊗ˢ o A ≅ ⊗[ o ] A whenever Split is the free
-- choice` (`canonical`).
-- ==================================================================

-- PRIMITIVE (phase 1)
split3app : {u v w : String} → Split3 u v w → u ++ v Eq.≡ w
split3app nil      = Eq.refl
split3app (cons s) = Eq.ap (_ ∷_) (split3app s)

-- PRIMITIVE (phase 1)
⊗ˢ→⊗ : {A : Bool → Gr} → ⊗ˢ appop A ⊢ ⊗[ appop ] A
⊗ˢ→⊗ w ((u , v , s) , h) = (λ b → if b then u else v) , split3app s , h

-- PRIMITIVE (phase 1)
⊗→⊗ˢ : {A : Bool → Gr} → ⊗[ appop ] A ⊢ ⊗ˢ appop A
⊗→⊗ˢ w (m⃗ , Eq.refl , h) =
  (m⃗ true , m⃗ false , splitAll (m⃗ true) (m⃗ false))
  , λ { true → h true ; false → h false }

-- ==================================================================
-- The SAME translation on the ℕ side.
--
-- `transportGF` below is stated at `ℕM.⊗[ appop ]`, because that is the
-- connective `ChangeOfTheory` speaks.  Every ℕ-side PROGRAM -- e.g. the
-- Dyck grammar in `Species.agda` -- is written at `⊗ˢ`.  Without this
-- pair the transport cannot be applied to anything actually written in
-- the calculus, which is why it belongs here and not in a downstream
-- file.  Mirrors `⊗ˢ→⊗` / `⊗→⊗ˢ` above with `Add3` for `Split3`.
-- ==================================================================

-- PRIMITIVE (phase 1)
⊗ˢᴺ→⊗ᴺ : {A : Bool → NatGr} → N.⊗ˢ appop A ℕM.⊢ ℕM.⊗[ appop ] A
⊗ˢᴺ→⊗ᴺ n ((i , j , a) , h) = (λ b → if b then i else j) , N.add3→+ a , h

-- PRIMITIVE (phase 1).  The `λ { true → … ; false → … }` is the arity-η
-- tax: `if a then m⃗ true else m⃗ false` is not definitionally `m⃗ a`.
⊗ᴺ→⊗ˢᴺ : {A : Bool → NatGr} → ℕM.⊗[ appop ] A ℕM.⊢ N.⊗ˢ appop A
⊗ᴺ→⊗ˢᴺ n (m⃗ , Eq.refl , h) =
  (m⃗ true , m⃗ false , N.addAll (m⃗ true) (m⃗ false))
  , λ { true → h true ; false → h false }

-- ==================================================================
-- THE PAYOFF.
-- ==================================================================

-- (0) Isomorphisms pull back for free -- `pull` is precomposition, so
-- there is literally nothing to do.  This is the additive half.
pullIso : {A B : NatGr} → ((n : ℕ) → Iso (A n) (B n))
        → (w : String) → Iso (pull A w) (pull B w)
pullIso i w = i (length w)

-- (1) The multiplicative half, in both directions.  The second is the
-- one that needs `lengthReflects`; over abelianisation it does not
-- exist.
-- Note every family below is passed EXPLICITLY.  This is the trap
-- recorded in CLAUDE.md ("grammar-valued implicits are not inferrable"):
-- `⊗ˢ appop (λ a → pull (B a))` unfolds to a Σ in which `B` occurs only
-- under `pull` and under `parts`, so no first-order unifier recovers it.
pull⊗ˢ : (B : Bool → NatGr)
       → ⊗ˢ appop (λ a → pull (B a)) ⊢ pull (ℕM.⊗[ appop ] B)
pull⊗ˢ B = pull⊗ appop {B = B} ∘g ⊗ˢ→⊗ {A = λ a → pull (B a)}

pull⊗ˢ⁻ : (B : Bool → NatGr)
        → pull (ℕM.⊗[ appop ] B) ⊢ ⊗ˢ appop (λ a → pull (B a))
pull⊗ˢ⁻ B = ⊗→⊗ˢ {A = λ a → pull (B a)}
          ∘g pull⊗⁻ lengthReflects appop {B = B}

-- (2) And in the binary notation programs are actually written in.
_ℕ⊗_ : NatGr → NatGr → NatGr
A ℕ⊗ B = ℕM.⊗[ appop ] (λ b → if b then A else B)

infixr 20 _ℕ⊗_

module _ (A B : NatGr) where

  private
    fam : Bool → NatGr
    fam b = if b then A else B

  pull⊗' : pull (A ℕ⊗ B) ⊢ (pull A ⊗' pull B)
  pull⊗' = ⊗ˢ-map appop {A = λ a → pull (fam a)}
                        {B = λ b → if b then pull A else pull B}
                        (λ { true → idg ; false → idg })
         ∘g pull⊗ˢ⁻ fam

  pull⊗'⁻ : (pull A ⊗' pull B) ⊢ pull (A ℕ⊗ B)
  pull⊗'⁻ = pull⊗ˢ fam
          ∘g ⊗ˢ-map appop {A = λ b → if b then pull A else pull B}
                          {B = λ a → pull (fam a)}
                          (λ { true → idg ; false → idg })

-- (3) THE STATEMENT WORTH READING.  A generating-function identity
--
--       A(x)  ≅  B(x) · C(x)
--
-- proved once over ℕ becomes an isomorphism of STRING GRAMMARS,
-- with no further work and no reference to strings in its proof.
transportGF : (A B C : NatGr)
            → (A ℕM.⊢ (B ℕ⊗ C)) → ((B ℕ⊗ C) ℕM.⊢ A)
            → (pull A ⊢ (pull B ⊗' pull C)) × ((pull B ⊗' pull C) ⊢ pull A)
transportGF A B C f g =
  pull⊗' B C ∘g pullTerm f , pullTerm g ∘g pull⊗'⁻ B C

-- ==================================================================
-- (4) ... AND IN THE FORM PROGRAMS ARE WRITTEN IN.
--
-- `transportGF` speaks `_ℕ⊗_`, the model-level convolution.  A ℕ-side
-- program -- `Species.agda`'s Dyck grammar, say -- is written with
-- `Nat/Connectives`' `_⊗'_`, which is `⊗ˢ`.  Composing with the bridge
-- above gives the version that actually applies to such a program, and
-- with it the Catalan recurrence transports to strings.
-- ==================================================================

module _ (A B : NatGr) where

  private
    famᴺ : Bool → NatGr
    famᴺ b = if b then A else B

  pull⊗ˢ' : pull (A N.⊗' B) ⊢ (pull A ⊗' pull B)
  pull⊗ˢ' = pull⊗' A B ∘g pullTerm (⊗ˢᴺ→⊗ᴺ {A = famᴺ})

  pull⊗ˢ'⁻ : (pull A ⊗' pull B) ⊢ pull (A N.⊗' B)
  pull⊗ˢ'⁻ = pullTerm (⊗ᴺ→⊗ˢᴺ {A = famᴺ}) ∘g pull⊗'⁻ A B
