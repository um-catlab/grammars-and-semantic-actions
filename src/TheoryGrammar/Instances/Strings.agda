{-
  THE STRING INSTANCE: LambekD recovered, with the constructions and
  theorems it actually contains.

  What is checked here, and how it compares to `Grammar/`:

    LambekD                      here                    cost
    -------                      ----                    ----
    _⊗_, ⊗-intro                 _⊗'_, ⊗-mk              same
    ε                            ε'                      same
    literal c                    ⌈ c ∷ [] ⌉              same
    _⟜_                          _⟜'_ (slot `false`)     same
    ⟜-app  (has Eq.transport)    ⟜-app                   NO transport
    ⟜UMP : Iso (A⊗B⊢C) (B⊢C⟜A)   ⟜UMP                    β refl, η funExt
    ⊗-unit-l                     ⊗-unit-l                REFL, one clause
    ⊗-unit-r (needs ++-unit-r)   ⊗-unit-r                one induction
    ⊗-assoc                      ⊗-assoc                 one induction
    KL*, star unrolling          KL*, unroll/roll        same

  The asymmetry between ⊗-unit-l (immediate) and ⊗-unit-r (needs an
  induction) is genuine and survives the generalisation -- it is the
  `Split3 u [] w → u ≡ w` direction, which is `++-unit-r` in disguise.
  That is the honest situation: the substrate presentation removes the
  transports, not the mathematics.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Strings where

open import Cubical.Foundations.Prelude
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
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

module Str (Char : Type₀) where

  String : Type₀
  String = List Char

  -- ================================================================
  -- Signature of monoids; splittings inductively.
  -- ================================================================

  data MonOp : Type₀ where
    nilop appop : MonOp

  MonAr : MonOp → Type₀
  MonAr nilop = ⊥
  MonAr appop = Bool

  monSig : SortedSig Unit ℓ-zero ℓ-zero
  monSig .ops          = MonOp
  monSig .arities      = MonAr
  monSig .sortOf _ _   = tt
  monSig .resultSort _ = tt

  data Split3 : String → String → String → Type₀ where
    nil  : ∀ {v} → Split3 [] v v
    cons : ∀ {c u v w} → Split3 u v w → Split3 (c ∷ u) v (c ∷ w)

  -- IsNil as a RECURSIVE predicate, not an indexed family: then every
  -- case split below happens on the string itself, and no clause needs
  -- higher-dimensional unification.
  IsNil : String → Type₀
  IsNil []      = Unit
  IsNil (_ ∷ _) = ⊥

  splitAll : (u v : String) → Split3 u v (u ++ v)
  splitAll []      v = nil
  splitAll (c ∷ u) v = cons (splitAll u v)

  MonSplit : (o : MonOp) → String → Type₀
  MonSplit nilop w = IsNil w
  MonSplit appop w = Σ[ u ∈ String ] Σ[ v ∈ String ] Split3 u v w

  MonParts : (o : MonOp) (w : String) → MonSplit o w → MonAr o → String
  MonParts nilop w sp ()
  MonParts appop w (u , v , _) b = if b then u else v

  strSub : Substrate monSig ℓ-zero ℓ-zero
  strSub .carrier _   = String
  strSub .op nilop _  = []
  strSub .op appop f  = f true ++ f false
  strSub .Split       = MonSplit
  strSub .parts       = MonParts
  strSub .split nilop f = tt
  strSub .split appop f = f true , f false , splitAll (f true) (f false)
  strSub .parts-split nilop f = funExt λ ()
  strSub .parts-split appop f = funExt λ { false → refl ; true → refl }

  open SubNotation strSub

  -- ================================================================
  -- LambekD's connectives.
  -- ================================================================

  Gr : Type₁
  Gr = TheoryTy ℓ-zero tt

  ε' : Gr
  ε' = ⊗ˢ nilop (λ ())

  _⊗'_ : Gr → Gr → Gr
  A ⊗' B = ⊗ˢ appop (λ b → if b then A else B)

  literal : Char → Gr
  literal c = ⌈ c ∷ [] ⌉

  infixr 20 _⊗'_

  -- intro and elim for ⊗
  ⊗-mk : {A B : Gr} {u v w : String} → Split3 u v w → A u → B v → (A ⊗' B) w
  ⊗-mk {u = u} {v} s a b = (u , v , s) , λ { true → a ; false → b }

  ⊗-elim : {A B C : Gr}
         → (∀ {u v w} → A u → B v → Split3 u v w → C w)
         → (A ⊗' B) ⊢ C
  ⊗-elim f w ((u , v , s) , h) = f (h true) (h false) s

  ε-mk : ε' []
  ε-mk = tt , λ ()

  -- ================================================================
  -- The residual, at slot `false` (the right factor).
  -- ================================================================

  focR : Focus strSub appop false
  focR .SplitAt v  = Σ[ u ∈ String ] Σ[ w ∈ String ] Split3 u v w
  focR .whole (u , w , _) = w
  focR .Rest       = Unit
  focR .restOf _   = true
  focR .restSlot (u , w , _) _ = u

  module R = FocusNotation focR

  _⟜'_ : Gr → Gr → Gr
  C ⟜' A = R.⊸ᶠ (λ b → if b then A else C) C

  -- ⟜-app.  LambekD's has `Eq.transport B (Eq.sym w≡w'++w'')`; this has
  -- nothing, because the splitting already names the whole.
  ⟜-app : {A C : Gr} → (A ⊗' (C ⟜' A)) ⊢ C
  ⟜-app w ((u , v , s) , h) = h false (u , w , s) (λ _ → h true)

  -- THE ADJUNCTION, as LambekD states it.
  module _ {A B C : Gr} where

    ⟜-intro : (A ⊗' B) ⊢ C → B ⊢ (C ⟜' A)
    ⟜-intro f v bv (u , w , s) g = f w (⊗-mk s (g tt) bv)

    ⟜-intro⁻ : B ⊢ (C ⟜' A) → (A ⊗' B) ⊢ C
    ⟜-intro⁻ h = ⊗-elim λ a bv s → h _ bv (_ , _ , s) (λ _ → a)

    -- β is definitional (Unit has η, so `λ _ → g tt` IS `g`)
    ⟜-β : (h : B ⊢ (C ⟜' A)) → ⟜-intro (⟜-intro⁻ h) ≡ h
    ⟜-β h = refl

    -- η needs funExt over the ARITY, because Bool has no η.  This is the
    -- one cost of encoding a binary operation as a Bool-indexed family.
    ⟜-η : (f : (A ⊗' B) ⊢ C) → ⟜-intro⁻ (⟜-intro f) ≡ f
    ⟜-η f = funExt λ w → funExt λ { ((u , v , s) , h) →
      cong (λ k → f w ((u , v , s) , k)) (funExt λ { true → refl ; false → refl }) }

    ⟜UMP : Iso ((A ⊗' B) ⊢ C) (B ⊢ (C ⟜' A))
    ⟜UMP .Iso.fun = ⟜-intro
    ⟜UMP .Iso.inv = ⟜-intro⁻
    ⟜UMP .Iso.sec = ⟜-β
    ⟜UMP .Iso.ret = ⟜-η

  -- ================================================================
  -- Unit and associativity.
  -- ================================================================

  -- left unit: one clause, no lemma.  `isNil` forces u = [], then `nil`
  -- forces w = v, and the payload is already at the right index.
  ⊗-unit-l : {A : Gr} → (ε' ⊗' A) ⊢ A
  ⊗-unit-l w (([]    , v , nil) , h) = h false
  ⊗-unit-l w ((c ∷ u , v , s)   , h) = E.rec (h true .fst)

  -- right unit: needs the induction that `++-unit-r` needs in LambekD.
  splitNilR : ∀ {u w} → Split3 u [] w → u Eq.≡ w
  splitNilR nil      = Eq.refl
  splitNilR (cons s) with splitNilR s
  ... | Eq.refl = Eq.refl

  ⊗-unit-r : {A : Gr} → (A ⊗' ε') ⊢ A
  ⊗-unit-r {A} w ((u , []    , s) , h) = coeA (splitNilR s) (h true)
    where coeA : ∀ {u' w'} → u' Eq.≡ w' → A u' → A w'
          coeA Eq.refl a = a
  ⊗-unit-r {A} w ((u , c ∷ v , s) , h) = E.rec (h false .fst)

  ⊗-unit-l⁻ : {A : Gr} → A ⊢ (ε' ⊗' A)
  ⊗-unit-l⁻ w a = ⊗-mk nil ε-mk a

  -- the round trip LambekD proves with a chain of Eq.transports
  ⊗-unit-ll⁻ : {A : Gr} → ∀ w (a : A w) → ⊗-unit-l w (⊗-unit-l⁻ {A = A} w a) ≡ a
  ⊗-unit-ll⁻ w a = refl

  -- associativity, by induction on the outer splitting
  splitAssoc : ∀ {u v v' x w} → Split3 u x w → Split3 v v' x
             → Σ[ y ∈ String ] (Split3 u v y × Split3 y v' w)
  splitAssoc nil      t = _ , nil , t
  splitAssoc (cons s) t =
    let (y , s1 , s2) = splitAssoc s t in _ , cons s1 , cons s2

  ⊗-assoc : {A B C : Gr} → (A ⊗' (B ⊗' C)) ⊢ ((A ⊗' B) ⊗' C)
  ⊗-assoc = ⊗-elim λ { a ((v , v' , t) , k) s →
    let (y , s1 , s2) = splitAssoc s t
    in ⊗-mk s2 (⊗-mk s1 a (k true)) (k false) }

  -- ================================================================
  -- THE GRADING.  `deg = length`, and a slot is proper exactly when its
  -- COMPLEMENT is nonempty -- for the monoid this is the only source of
  -- non-proper splittings, and it is the unit's doing: `(ε , w)` and
  -- `(w , ε)` are splittings of `w` with a trivial part.
  -- ================================================================

  split3LenL : ∀ {u v w} → Split3 u v w → length u ≤ length w
  split3LenL nil      = zero-≤
  split3LenL (cons s) = suc-≤-suc (split3LenL s)

  split3LenR : ∀ {u v w} → Split3 u v w → length v ≤ length w
  split3LenR nil      = ≤-refl
  split3LenR (cons s) = ≤-suc (split3LenR s)

  split3LenL< : ∀ {u v w} → Split3 u v w → 0 < length v → length u < length w
  split3LenL< nil      pr = pr
  split3LenL< (cons s) pr = suc-≤-suc (split3LenL< s pr)

  split3LenR< : ∀ {u v w} → Split3 u v w → 0 < length u → length v < length w
  split3LenR< nil      pr = E.rec (¬-<-zero pr)
  split3LenR< (cons s) pr = suc-≤-suc (split3LenR s)

  StrProper : (o : MonOp) (m : String) → MonSplit o m → MonAr o → Type₀
  StrProper nilop m sp ()
  StrProper appop w (u , v , _) b = 0 < length (if b then v else u)

  strGraded : GradedSubstrate monSig ℓ-zero ℓ-zero
  strGraded .sub    = strSub
  strGraded .deg _  = length
  strGraded .Proper = StrProper
  strGraded .deg≤ nilop m sp ()
  strGraded .deg≤ appop m (u , v , s) true  = split3LenL s
  strGraded .deg≤ appop m (u , v , s) false = split3LenR s
  strGraded .deg< nilop m sp ()
  strGraded .deg< appop m (u , v , s) true  pr = split3LenL< s pr
  strGraded .deg< appop m (u , v , s) false pr = split3LenR< s pr

  -- ================================================================
  -- ENUMERATION OF SPLITTINGS.  Derivable, not assumed: the splittings
  -- of `w` are its `length w + 1` cuts.
  -- ================================================================

  data _∈L_ {X : Type₀} (x : X) : List X → Type₀ where
    here  : ∀ {xs} → x ∈L (x ∷ xs)
    there : ∀ {y xs} → x ∈L xs → x ∈L (y ∷ xs)

  ∈map : {X Y : Type₀} (f : X → Y) {x : X} {xs : List X}
       → x ∈L xs → f x ∈L map f xs
  ∈map f here      = here
  ∈map f (there p) = there (∈map f p)

  cuts : (w : String) → List (MonSplit appop w)
  cuts []      = ([] , [] , nil) ∷ []
  cuts (c ∷ w) =
    ([] , c ∷ w , nil) ∷ map (λ { (u , v , s) → (c ∷ u , v , cons s) }) (cuts w)

  cutsComplete : {u v w : String} (s : Split3 u v w) → (u , v , s) ∈L cuts w
  cutsComplete {v = []}    nil = here
  cutsComplete {v = _ ∷ _} nil = here
  cutsComplete (cons s)        = there (∈map _ (cutsComplete s))

  enumSplit : (o : MonOp) (m : String) → List (MonSplit o m)
  enumSplit nilop []      = tt ∷ []
  enumSplit nilop (_ ∷ _) = []
  enumSplit appop w       = cuts w

  enumComplete : (o : MonOp) (m : String) (sp : MonSplit o m) → sp ∈L enumSplit o m
  enumComplete nilop []      tt = here
  enumComplete appop w (u , v , s) = cutsComplete s

  -- ================================================================
  -- Kleene star.  NOT a bespoke datatype: it is the generic μ at the
  -- description  ε ⊕ (A ⊗ Var)  in the functor language of
  -- TheoryGrammar.Inductive.  Only `nil*`, `cons*` and `unroll*` look at
  -- representations -- they are the star's PRIMITIVES.  Everything built
  -- from the star is then point-free.
  -- ================================================================

  open Guard strGraded ℓ-zero Unit (λ _ → tt)

  starSlot : Gr → Bool → Functor tt
  starSlot A true  = ⌜ A ⌝
  starSlot A false = Var tt

  starAlt : Gr → Bool → Functor tt
  starAlt A true  = ⌜ ε' ⌝
  starAlt A false = ⊗e appop (starSlot A)

  starF : Gr → Unit → Functor tt
  starF A _ = ⊕e Bool (starAlt A)

  -- ================================================================
  -- THE UNIT versus GUARDEDNESS.  `A *` is guarded exactly when `A` is
  -- NON-NULLABLE.  If `A` accepts ε then the splitting `(ε , w)` puts
  -- the recursive occurrence back at `w`, and the star has infinitely
  -- many parses at every index -- the classic `(ε)*` problem.  The type
  -- `μ (starF A)` still exists and every tree in it is finite; it is
  -- enumeration and `hyloC` that fail.  So the unit is harmless as an
  -- operation and dangerous only through the fixpoint, and this is the
  -- hypothesis that fences it off.
  -- ================================================================

  NonNullable : Gr → Type₀
  NonNullable A = (u : String) → A u → 0 < length u

  starGuarded : (A : Gr) → NonNullable A → (x : Unit) → Guarded (starF A x)
  starGuarded A nn tt = <⊕e Bool (starAlt A) alt
    where
      go : (m : String) (sp : MonSplit appop m)
           (sh : (a : Bool) → Sh (starSlot A a) (MonParts appop m sp a))
           (a : Bool) (p : Pos (starSlot A a) _ (sh a))
         → degIx (nx (starSlot A a) _ (sh a) p) < length m
      go m sp sh true ()
      go m (u , v , s) sh false p =
        slotProper appop m (u , v , s) false (≤Var tt)
                   (nn u (lower (sh true))) (sh false) p

      alt : (b : Bool) → Guarded (starAlt A b)
      alt true  = <⌜⌝ ε'
      alt false = ⊗-guard appop (starSlot A) go

  -- literals are non-nullable, so `literal c *` is guarded
  literalNN : (c : Char) → NonNullable (literal c)
  literalNN c .(c ∷ []) Eq.refl = ≤-refl

  KL* : Gr → Gr
  KL* A w = μ (starF A) (tt , w)

  module _ {A : Gr} where

    nil* : ε' ⊢ KL* A
    nil* w e = sup (true , lift e) λ ()

    cons* : (A ⊗' KL* A) ⊢ KL* A
    cons* w ((u , v , s) , h) =
      sup (false , (u , v , s) , λ { true → lift (h true) ; false → tt* })
          λ { (true  , ()) ; (false , _) → h false }

    unroll* : KL* A ⊢ (ε' ⊕ (A ⊗' KL* A))
    unroll* w t with unroll t
    ... | (true  , e)        , f = inl (lower e)
    ... | (false , sp , sh)  , f =
      inr (sp , λ { true → lower (sh true) ; false → f (false , tt*) })

  -- The star algebra, point-free: this is `roll` for the star.
  roll* : {A : Gr} → (ε' ⊕ (A ⊗' KL* A)) ⊢ KL* A
  roll* = ⊕-E nil* cons*
    where ⊕-E : {P Q R : Gr} → P ⊢ R → Q ⊢ R → (P ⊕ Q) ⊢ R
          ⊕-E f g w (inl x) = f w x
          ⊕-E f g w (inr y) = g w y

-- ==================================================================
-- A concrete parse that computes.
-- ==================================================================

module Example where

  open Str Bool

  -- the grammar `a b` over the two-letter alphabet
  ab : Gr
  ab = literal true ⊗' literal false

  parse-ab : ab (true ∷ false ∷ [])
  parse-ab = ⊗-mk (cons nil) Eq.refl Eq.refl

  -- a two-element star, built from the star's combinators rather than
  -- from constructors of a bespoke datatype
  aa : KL* (literal true) (true ∷ true ∷ [])
  aa = cons* _ (⊗-mk (cons nil) Eq.refl
         (cons* _ (⊗-mk (cons nil) Eq.refl
           (nil* _ ε-mk))))
