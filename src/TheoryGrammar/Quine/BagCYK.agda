{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CYK OVER A COMMUTATIVE THEORY.

  `Instances.Strings.CYK` verbatim, with the free monoid replaced by the
  free COMMUTATIVE monoid: `bagFib` for `strFib`, `Ilv` for `Split3`.
  Everything else -- the description, the guardedness, the `löb`, the
  chart -- is untouched, because none of it ever mentioned the splitting
  relation.  That is the point of the exercise; the diff is:

      cuts w        n+1 prefixes                allIlv w      2ⁿ subsets

  and nothing else.  So the ONE thing a commutative theory costs is the
  size of the cut space, and it is paid here, once.

  What it BUYS shows up in the grammar rather than in this file: a
  binary rule `P → Q T` no longer says "a Q then a T", it says "a Q part
  and a T part", and `⊗-comm` (`Instances.Bags.Commutativity`) is a term.
  A parse is a PARTITION of the bag, not a cut of a list.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Quine.BagCYK (Char : Type₀) where

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
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.View
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Guarded
import TheoryGrammar.Decidable.Enumerated as DE
open DE using (module DecEnum)

open import TheoryGrammar.Instances.Bags.Graded Char public

open Views bagFib public

-- The constant former's level coercion (`⟦ ⌜ B ⌝ ⟧c A m = Lift _ (B m)`).
-- `liftg` already exists (`Bags.Connectives`); these are its type and
-- its inverse, which the bag instance had never needed before.
Liftg : Gr → Gr
Liftg A m = Lift ℓ-zero (A m)

lowerg : {A : Gr} → Liftg A ⊢ A
lowerg _ = lower

-- the cut search, and the two abbreviations its hypothesis is stated in
open DecEnum  bagFib    using (⊗at; Refutes; dec-⊗-cuts; slotMiss)
open DecGuard bagGraded using (SortFam; ▷ᴬ; löbᵍ; dec-⊗▷; resourceOf)

-- ==================================================================
-- §0  THE SPLITTINGS ARE FINITELY ENUMERABLE -- and this is the ONE
--     place commutativity costs anything.  A bag of `n` elements has
--     `2ⁿ` interleavings against a string's `n+1` cuts.
-- ==================================================================

allIlv : (w : Bag) → List (Σ[ u ∈ Bag ] Σ[ v ∈ Bag ] Ilv u v w)
allIlv []      = ([] , [] , nil) ∷ []
allIlv (x ∷ w) =
     map (λ { (u , v , s) → (x ∷ u , v , left s)  }) (allIlv w)
  ++ map (λ { (u , v , s) → (u , x ∷ v , right s) }) (allIlv w)

allIlvComplete : {u v w : Bag} (s : Ilv u v w) → (u , v , s) ∈L allIlv w
allIlvComplete nil       = here
allIlvComplete (left s)  = ∈++ˡ (∈map _ (allIlvComplete s))
allIlvComplete (right s) = ∈++ʳ _ (∈map _ (allIlvComplete s))

cuts : (o : MonOp) (m : Bag) → List (MonSplit o m)
cuts nilop []      = tt ∷ []
cuts nilop (_ ∷ _) = []
cuts appop w       = allIlv w

enumComplete : (o : MonOp) (m : Bag) (sp : MonSplit o m) → sp ∈L cuts o m
enumComplete nilop []            tt        = here
enumComplete appop w (u , v , s)           = allIlvComplete s

-- ==================================================================
-- §1  THE RESOURCE LAW and the arity's enumeration.  Verbatim
--     `Strings.Graded`; neither mentions a splitting relation.
-- ==================================================================

ntProper : (w : Bag) (sp : MonSplit appop w)
         → ((a : Bool) → NonTrivial (MonParts appop w sp a))
         → (a : Bool) → Proper' appop w sp a
ntProper w sp h true  = h false
ntProper w sp h false = h true

appAr : List Bool
appAr = true ∷ false ∷ []

appArComplete : (a : Bool) → a ∈L appAr
appArComplete true  = here
appArComplete false = there here

-- ==================================================================
-- §2  THE DECOMPOSITION AXIOM.  Every bag is empty or has an element
--     pulled off -- and which element is pulled off is arbitrary, which
--     is why every algebra downstream had better be commutative.
--
--     PRIMITIVE (phase 1): matching the carrier is what a `Cover` is
--     for, and its type is internal.
-- ==================================================================

bagCase : Cover (⌈ [] ⌉ ⊕ NonTrivial)
bagCase []       _ = inl Eq.refl
bagCase (x ∷ xs) _ = inr (x , ⊗-mk (left (ilvApp [] xs)) Eq.refl tt)

decNTv : Cover (NonTrivial ⊕ ⌈ [] ⌉)
decNTv = caseOf bagCase ⊕-I₂ ⊕-I₁

-- PRIMITIVE (phase 1): the empty bag is trivial.
¬NT[] : No (NonTrivial [])
¬NT[] ne = E.rec (¬-<-zero (ntLen ne))

probe-NT : Probe NonTrivial
probe-NT = caseOf decNTv
             (dec-yes NonTrivial)
             (⌈⌉-E {a = []} {B = Dec⟨ NonTrivial ⟩} (dec-no NonTrivial [] ¬NT[]))

-- ==================================================================
-- §3  THE GRAMMAR, ITS PARSE TREES, AND ITS DECISION.
--
--     Line for line `Instances.Strings.CYK`.  A "binary rule" `P → Q T`
--     is `⊗ˢ appop`, and at bags that means a PARTITION.
-- ==================================================================

module CYK (V : Type₀)
           (unitR : V → Char → Type₀)          -- P → c
           (binR  : V → V → V → Type₀) where   -- P → Q T

  module G = Guard bagGraded ℓ-zero V (λ _ → tt)

  Rule : V → Type₀
  Rule P = (Σ[ c ∈ Char ] unitR P c) ⊎ (Σ[ Q ∈ V ] Σ[ T ∈ V ] binR P Q T)

  NEslot : V → Bool → G.Functor tt
  NEslot Q true  = G.Var Q
  NEslot Q false = G.⌜ NonTrivial ⌝

  NEvar : V → G.Functor tt
  NEvar Q = G.&e Bool (NEslot Q)

  binSlot : V → V → Bool → G.Functor tt
  binSlot Q T true  = NEvar Q
  binSlot Q T false = NEvar T

  ruleF : (P : V) → Rule P → G.Functor tt
  ruleF P (inl (c , _))     = G.⌜ ⌈ c ∷ [] ⌉ ⌝
  ruleF P (inr (Q , T , _)) = G.⊗e appop (binSlot Q T)

  CYKF : (P : V) → G.Functor tt
  CYKF P = G.⊕e (Rule P) (ruleF P)

  Deriv : V → Gr
  Deriv P w = G.μ CYKF (P , w)

  Der : G.Ix → Type₀
  Der = G.μ CYKF

  Layer : V → Gr
  Layer P = G.⟦ CYKF P ⟧c Der

  RuleG : (P : V) → Rule P → Gr
  RuleG P r = G.⟦ ruleF P r ⟧c Der

  SlotG : V → Gr
  SlotG Q = G.⟦ NEvar Q ⟧c Der

  binSlots : V → V → Bool → Gr
  binSlots Q T a = G.⟦ binSlot Q T a ⟧c Der

  unrollD : (P : V) → Deriv P ⊢ Layer P
  unrollD P w t = G.toC (CYKF P) w (G.unroll t)

  rollD : (P : V) → Layer P ⊢ Deriv P
  rollD P w t = G.roll (G.fromC (CYKF P) w t)

  neOf : (Q : V) → SlotG Q ⊢ NonTrivial
  neOf Q = lowerg ∘g &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} false

  derOf : (Q : V) → SlotG Q ⊢ Deriv Q
  derOf Q = &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} true

  -- PRIMITIVE (phase 1): `neOf` at the level of SHAPES.
  neOfSh : (Q : V) (w : Bag) → G.Sh (NEvar Q) w → NonTrivial w
  neOfSh Q w sh = lower (sh false)

  ≤NEslot : (Q : V) (b : Bool) → G.Guarded≤ (NEslot Q b)
  ≤NEslot Q true  = G.≤Var Q
  ≤NEslot Q false = G.≤⌜⌝ NonTrivial

  ≤binSlot : (Q T : V) (b : Bool) → G.Guarded≤ (binSlot Q T b)
  ≤binSlot Q T true  = G.≤&e Bool (NEslot Q) (≤NEslot Q)
  ≤binSlot Q T false = G.≤&e Bool (NEslot T) (≤NEslot T)

  cykGuarded : (P : V) → G.Guarded (CYKF P)
  cykGuarded P = G.<⊕e (Rule P) (ruleF P) alt
    where
      pr : (Q T : V) (m : Bag) (sp : MonSplit appop m)
           (sh : (a : Bool) → G.Sh (binSlot Q T a) (MonParts appop m sp a))
           (a : Bool) → G.Pos (binSlot Q T a) _ (sh a) → Proper' appop m sp a
      pr Q T m sp sh true  p = neOfSh T (MonParts appop m sp false) (sh false)
      pr Q T m sp sh false p = neOfSh Q (MonParts appop m sp true)  (sh true)

      alt : (r : Rule P) → G.Guarded (ruleF P r)
      alt (inl (c , _))     = G.<⌜⌝ ⌈ c ∷ [] ⌉
      alt (inr (Q , T , _)) =
        G.<⊗e appop (binSlot Q T) (≤binSlot Q T) (pr Q T)

module Parser (V : Type₀)
              (unitR : V → Char → Type₀)
              (binR  : V → V → V → Type₀) where

  open CYK V unitR binR public

  -- the two constructors of a parse tree, as terms
  leaf : {P : V} {w : Bag} (c : Char) → unitR P c
       → w Eq.≡ c ∷ [] → Deriv P w
  leaf c pf q = G.sup (inl (c , pf) , lift q) λ ()

  node : {P Q T : V} {w u v : Bag} → binR P Q T → Ilv u v w
       → NonTrivial u → NonTrivial v → Deriv Q u → Deriv T v → Deriv P w
  node {Q = Q} {T} {u = u} {v} pf s neu nev tq tT =
    G.sup ( inr (Q , T , pf)
          , ((u , v , s) , λ { true  → λ { true → tt* ; false → lift neu }
                             ; false → λ { true → tt* ; false → lift nev } }) )
          λ { (true  , (true  , _)) → tq
            ; (false , (true  , _)) → tT
            ; (true  , (false , ()))
            ; (false , (false , ())) }

  module Decide (allRules    : (P : V) → List (Rule P))
                (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
                (litProbe    : (c : Char) → Probe ⌈ c ∷ [] ⌉) where

    Chart : Gr
    Chart = &ᴰ V (λ P → Dec⟨ Deriv P ⟩)

    ChartF : SortFam ℓ-zero
    ChartF _ = Chart

    chartAt : (P : V) → Chart ⊢ Dec⟨ Deriv P ⟩
    chartAt P = &ᴰ-E V {B = λ Q → Dec⟨ Deriv Q ⟩} P

    decLit : (c : Char) → Probe (Liftg ⌈ c ∷ [] ⌉)
    decLit c = dec-map ⌈ c ∷ [] ⌉ (Liftg ⌈ c ∷ [] ⌉) liftg lowerg ∘g litProbe c

    decSlot : (Q : V) → Chart ⊢ Dec⟨ SlotG Q ⟩
    decSlot Q =
      dec-&ᴰ (λ b → G.⟦ NEslot Q b ⟧c Der)
      ∘g &ᴰ-I {B = λ b → Dec⟨ G.⟦ NEslot Q b ⟧c Der ⟩}
               λ { true  → chartAt Q
                 ; false → dec-map NonTrivial (Liftg NonTrivial) liftg lowerg
                           ∘g probe-NT ∘g ⊤-I }

    decBin : (Q T : V) → ▷ᴬ ChartF ⊢ Dec⟨ ⊗ˢ appop (binSlots Q T) ⟩
    decBin Q T =
      dec-⊗▷ appop (binSlots Q T) ChartF
             (cuts appop) (enumComplete appop)
             (resourceOf appop (binSlots Q T) (λ _ → NonTrivial) (λ _ → probe-NT)
                         (λ { true → neOf Q ; false → neOf T })
                         ntProper appAr appArComplete)
             (λ m sp d → decΠBool (d true) (d false))
             λ { true → decSlot Q ; false → decSlot T }

    decRule : (P : V) (r : Rule P) → ▷ᴬ ChartF ⊢ Dec⟨ RuleG P r ⟩
    decRule P (inl (c , _))     = decLit c ∘g ⊤-I
    decRule P (inr (Q , T , _)) = decBin Q T

    decRow : (P : V) → ▷ᴬ ChartF ⊢ Dec⟨ Deriv P ⟩
    decRow P =
      dec-map (Layer P) (Deriv P) (rollD P) (unrollD P)
      ∘g dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P)
      ∘g &ᴰ-I {B = λ r → Dec⟨ RuleG P r ⟩} (decRule P)

    step : ▷ᴬ ChartF ⊢ Chart
    step = &ᴰ-I {B = λ P → Dec⟨ Deriv P ⟩} decRow

    chart : Cover Chart
    chart = löbᵍ ChartF (λ _ → step) tt

    derives? : (P : V) → Probe (Deriv P)
    derives? P = chartAt P ∘g chart

    derivesDec : (P : V) → Decision (Deriv P) (¬G (Deriv P))
    derivesDec P = decDefault (Deriv P) (derives? P)

    parse : (P : V) → Cover (MaybeG (Deriv P))
    parse P = toMaybe (Deriv P) ∘g derives? P
