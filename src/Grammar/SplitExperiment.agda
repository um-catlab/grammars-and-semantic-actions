open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.SplitExperiment (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC

-- ==================================================================
-- 1.  Splitting as an inductive family, not the equation w ≡ u ++ v.
-- ==================================================================

data Split : String → String → String → Type ℓ-zero where
  nil  : ∀ {v} → Split [] v v
  cons : ∀ {c u v w} → Split u v w → Split (c ∷ u) v (c ∷ w)

-- ==================================================================
-- 2.  The connectives.  Nothing below mentions _++_.
-- ==================================================================

data Eps : String → Type ℓ-zero where
  mk : Eps []

data Lit (c : ⟨ Alphabet ⟩) : String → Type ℓ-zero where
  mk : Lit c (c ∷ [])

lit-inv : ∀ {d c w} → Lit d (c ∷ w) → (c ≡ d) × Eps w
lit-inv mk = refl , mk

⊥G : Grammar ℓ-zero
⊥G _ = ⊥

⊤G : Grammar ℓ-zero
⊤G _ = Unit

_⊗'_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(A ⊗' B) w = Σ[ u ∈ String ] Σ[ v ∈ String ] Split u v w × A u × B v

_⟜'_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(A ⟜' B) v = ∀ u w → B u → Split u v w → A w

_⊕G_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(A ⊕G B) w = A w ⊎ B w

_&G_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(A &G B) w = A w × B w

data KStar (A : Grammar ℓA) : String → Type ℓA where
  nil  : KStar A []
  cons : ∀ {u v w} → Split u v w → A u → KStar A v → KStar A w

-- ==================================================================
-- 3.  Application needs no transport.
-- ==================================================================

⟜'-app : A ⊗' (B ⟜' A) ⊢ B
⟜'-app w (u , v , s , a , f) = f u w a s

⟜'-intro : A ⊗' B ⊢ C → B ⊢ C ⟜' A
⟜'-intro f v b u w a s = f w (u , v , s , a , b)

-- ==================================================================
-- 4.  Agreement with the equation presentation.
-- ==================================================================

Split→Eq : ∀ {u v w} → Split u v w → w Eq.≡ u ++ v
Split→Eq nil      = Eq.refl
Split→Eq (cons s) = Eq.ap (_ ∷_) (Split→Eq s)

Eq→Split : ∀ {u v w} → w Eq.≡ u ++ v → Split u v w
Eq→Split {u = []}     Eq.refl = nil
Eq→Split {u = c ∷ u'} Eq.refl = cons (Eq→Split Eq.refl)

-- ==================================================================
-- 5.  The derivative, and its laws.  Every proof is by matching on a
--     Split or KStar derivation; none inverts an equation.
-- ==================================================================

δ : ⟨ Alphabet ⟩ → Grammar ℓA → Grammar ℓA
δ c A w = A (c ∷ w)

-- nullability
ν : Grammar ℓA → Type ℓA
ν A = A []

δ-⊥ : (c : ⟨ Alphabet ⟩) → δ c ⊥G ⊢ ⊥G
δ-⊥ c w x = x

δ-eps : (c : ⟨ Alphabet ⟩) → δ c Eps ⊢ ⊥G
δ-eps c w ()

δ-lit→ : (c d : ⟨ Alphabet ⟩) (w : String) → δ c (Lit d) w → (c Eq.≡ d) × Eps w
δ-lit→ c .c .[] mk = Eq.refl , mk

δ-⊕ : (c : ⟨ Alphabet ⟩) → δ c (A ⊕G B) ⊢ (δ c A ⊕G δ c B)
δ-⊕ c w x = x

δ-& : (c : ⟨ Alphabet ⟩) → δ c (A &G B) ⊢ (δ c A &G δ c B)
δ-& c w x = x

-- a constant grammar, for the nullability factor
_×G_ : Type ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
(X ×G B) w = X × B w

-- the case that was hard: δ (A ⊗ B) ≅ δA ⊗ B ⊕ νA × δB
δ-⊗→ : (c : ⟨ Alphabet ⟩) → δ c (A ⊗' B) ⊢ ((δ c A ⊗' B) ⊕G (ν A ×G δ c B))
δ-⊗→ c w (_ , _ , nil    , a , b) = inr (a , b)
δ-⊗→ c w (_ , v , cons s , a , b) = inl (_ , v , s , a , b)

δ-⊗← : (c : ⟨ Alphabet ⟩) → ((δ c A ⊗' B) ⊕G (ν A ×G δ c B)) ⊢ δ c (A ⊗' B)
δ-⊗← c w (inl (u , v , s , a , b)) = (c ∷ u , v , cons s , a , b)
δ-⊗← c w (inr (a , b))             = ([] , c ∷ w , nil , a , b)

-- the star: δ (A *) ≅ δ A ⊗ (A *), by recursion on the KStar derivation.
-- No non-nullability hypothesis is needed in this direction.
δ-*→ : (c : ⟨ Alphabet ⟩) → δ c (KStar A) ⊢ (δ c A ⊗' KStar A)
δ-*→ c w (cons nil      a k) = δ-*→ c w k
δ-*→ c w (cons (cons s) a k) = (_ , _ , s , a , k)

δ-*← : (c : ⟨ Alphabet ⟩) → (δ c A ⊗' KStar A) ⊢ δ c (KStar A)
δ-*← c w (u , v , s , a , k) = cons (cons s) a k

-- nullability of ⊗: splitting [] can only be nil
ν-⊗→ : ν (A ⊗' B) → ν A × ν B
ν-⊗→ (_ , _ , nil , a , b) = a , b

ν-⊗← : ν A × ν B → ν (A ⊗' B)
ν-⊗← (a , b) = [] , [] , nil , a , b

-- ==================================================================
-- 6.  A syntax, its syntactic derivative, and a total parser.
-- ==================================================================

open import Cubical.Relation.Nullary.Base

module Parser (_≟_ : Discrete ⟨ Alphabet ⟩) where

  data RegExp : Type ℓ-zero where
    rε r⊥ : RegExp
    rlit  : ⟨ Alphabet ⟩ → RegExp
    _r⊕_ _r⊗_ : RegExp → RegExp → RegExp
    r*    : RegExp → RegExp

  ⟦_⟧ : RegExp → Grammar ℓ-zero
  ⟦ rε ⟧      = Eps
  ⟦ r⊥ ⟧      = ⊥G
  ⟦ rlit c ⟧  = Lit c
  ⟦ r r⊕ s ⟧  = ⟦ r ⟧ ⊕G ⟦ s ⟧
  ⟦ r r⊗ s ⟧  = ⟦ r ⟧ ⊗' ⟦ s ⟧
  ⟦ r* r ⟧    = KStar ⟦ r ⟧

  ν? : (r : RegExp) → Dec (ν ⟦ r ⟧)
  ν? rε        = yes mk
  ν? r⊥        = no (λ ())
  ν? (rlit c)  = no (λ ())
  ν? (r r⊕ s) with ν? r | ν? s
  ... | yes a | _     = yes (inl a)
  ... | no ¬a | yes b = yes (inr b)
  ... | no ¬a | no ¬b = no λ { (inl a) → ¬a a ; (inr b) → ¬b b }
  ν? (r r⊗ s) with ν? r | ν? s
  ... | no ¬a | _     = no λ x → ¬a (ν-⊗→ x .fst)
  ... | yes a | no ¬b = no λ x → ¬b (ν-⊗→ x .snd)
  ... | yes a | yes b = yes (ν-⊗← (a , b))
  ν? (r* r)    = yes nil

  δ' : ⟨ Alphabet ⟩ → RegExp → RegExp
  δ' c rε       = r⊥
  δ' c r⊥       = r⊥
  δ' c (rlit d) with c ≟ d
  ... | yes _ = rε
  ... | no  _ = r⊥
  δ' c (r r⊕ s) = δ' c r r⊕ δ' c s
  δ' c (r r⊗ s) with ν? r
  ... | yes _ = (δ' c r r⊗ s) r⊕ δ' c s
  ... | no  _ = δ' c r r⊗ s
  δ' c (r* r)   = δ' c r r⊗ r* r

  δ'→ : (c : ⟨ Alphabet ⟩) (r : RegExp) (w : String)
    → ⟦ δ' c r ⟧ w → ⟦ r ⟧ (c ∷ w)
  δ'→ c rε w ()
  δ'→ c r⊥ w ()
  δ'→ c (rlit d) w x with c ≟ d
  δ'→ c (rlit d) w x | yes p = lit-yes x
    where
      lit-yes : Eps w → Lit d (c ∷ w)
      lit-yes mk = subst (λ z → Lit z (c ∷ [])) p mk
  δ'→ c (rlit d) w x | no ¬p = Empty.rec x
  δ'→ c (r r⊕ s) w (inl x) = inl (δ'→ c r w x)
  δ'→ c (r r⊕ s) w (inr y) = inr (δ'→ c s w y)
  δ'→ c (r r⊗ s) w x with ν? r
  δ'→ c (r r⊗ s) w (inl (u , v , sp , dr , ss)) | yes a =
    c ∷ u , v , cons sp , δ'→ c r u dr , ss
  δ'→ c (r r⊗ s) w (inr y) | yes a =
    [] , c ∷ w , nil , a , δ'→ c s w y
  δ'→ c (r r⊗ s) w (u , v , sp , dr , ss) | no ¬a =
    c ∷ u , v , cons sp , δ'→ c r u dr , ss
  δ'→ c (r* r) w (u , v , sp , dr , k) = cons (cons sp) (δ'→ c r u dr) k

  δ'← : (c : ⟨ Alphabet ⟩) (r : RegExp) (w : String)
    → ⟦ r ⟧ (c ∷ w) → ⟦ δ' c r ⟧ w
  δ'← c rε w ()
  δ'← c r⊥ w ()
  δ'← c (rlit d) w x with c ≟ d
  δ'← c (rlit d) w x | yes p = lit-inv x .snd
  δ'← c (rlit d) w x | no ¬p = ¬p (lit-inv x .fst)
  δ'← c (r r⊕ s) w (inl x) = inl (δ'← c r w x)
  δ'← c (r r⊕ s) w (inr y) = inr (δ'← c s w y)
  δ'← c (r r⊗ s) w x with ν? r
  δ'← c (r r⊗ s) w (_ , _ , nil     , a , b) | yes _  = inr (δ'← c s w b)
  δ'← c (r r⊗ s) w (_ , v , cons sp , a , b) | yes _  =
    inl (_ , v , sp , δ'← c r _ a , b)
  δ'← c (r r⊗ s) w (_ , _ , nil     , a , b) | no ¬a = Empty.rec (¬a a)
  δ'← c (r r⊗ s) w (_ , v , cons sp , a , b) | no ¬a =
    _ , v , sp , δ'← c r _ a , b
  -- reuse the semantic law δ-*→, whose own recursion over the KStar
  -- derivation is already accepted; the recursion here is on r.
  δ'← c (r* r) w x =
    let (u , v , sp , a , k) = δ-*→ c w x
    in u , v , sp , δ'← c r u a , k

  decMap : {X Y : Type ℓ-zero} → (X → Y) → (Y → X) → Dec X → Dec Y
  decMap f g (yes x) = yes (f x)
  decMap f g (no ¬x) = no (λ y → ¬x (g y))

  -- structural recursion on the string; δ' consumes exactly one character
  parse : (r : RegExp) (w : String) → Dec (⟦ r ⟧ w)
  parse r []      = ν? r
  parse r (c ∷ w) = decMap (δ'→ c r w) (δ'← c r w) (parse (δ' c r) w)
