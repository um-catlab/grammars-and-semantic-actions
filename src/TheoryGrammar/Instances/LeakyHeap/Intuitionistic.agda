{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE UNIT LAW FAILS, AND THE MONAD IT LEAVES BEHIND IS THE PASSAGE FROM
  CLASSICAL TO INTUITIONISTIC SEPARATION LOGIC.

  This is question 3 of `LeakyHeap/Base`'s table, and it is the one worth
  the effort.  `Affine/Base` found that `adrop` breaks `A ⊛ 𝟙 ⊢ A` and
  turns `A ⊛ 𝟙` into a nontrivial monad `⇓` whose algebras it called the
  AFFINE grammars.  The same thing happens here, one constructor for one
  constructor -- but on the separation-logic side the monad is not a new
  invention.  It already has a name, and two of them:

      ⇓ A  =  A ∗ emp                    "A holds of SOME sub-heap"

  ------------------------------------------------------------------
  §A  WHAT `⇓` IS.

  `emp` is `⊗ˢ nilop`, so `emp v` is `IsNil v`.  Unfolding `A ∗ emp` at a
  heap `h`,

      (A ∗ emp) h  =  Σ[ u ] Σ[ v ] SubIlv u v h × (u # v) × A u × IsNil v
                   ≅  Σ[ u ] (u ⊑ h) × A u

  where `u ⊑ h` -- spelled `SubIlv u [] h` -- says `u` is a SUB-HEAP of
  `h`: every cell of `u` is a cell of `h`, and `h` may have more.  (The
  `u # v` conjunct contributes nothing once `v` is empty, `#-nil`; this
  is the precise sense in which the unit law and the no-point theorem
  read DIFFERENT conjuncts of `LeakySplit`, hence the different axes of
  `Base`'s table.)

  So `⇓ A` is the UPWARD CLOSURE of `A` in the sub-heap order.  Both
  maps of the isomorphism are `⇓→sub`/`sub→⇓` below.

  ------------------------------------------------------------------
  §B  IT IS AN IDEMPOTENT MONAD -- i.e. A CLOSURE OPERATOR.

      ⇓-unit : A ⊢ ⇓ A                  keep everything (`subIlv-nilR`)
      ⇓-mult : ⇓ (⇓ A) ⊢ ⇓ A            transitivity of `⊑` (`subIlv-mono`)
      ⇓-map  : A ⊢ B → ⇓ A ⊢ ⇓ B        `∗-map`, i.e. the FRAME RULE

  and `⇓-idem` gives the converse of `⇓-mult`, so `⇓ (⇓ A) ⊣⊢ ⇓ A`.  A
  monad that is idempotent is a closure operator, and that is the honest
  description: `⇓` closes a predicate upward.

  ------------------------------------------------------------------
  §C  ITS ALGEBRAS ARE THE INTUITIONISTIC PREDICATES.

      Intuitionistic A  =  ⇓ A ⊢ A
      UpClosed A        =  u ⊑ w → A u → A w

  `alg→up` and `up→alg` show these are the same thing (§4).  "Upward
  closed in the sub-heap order" is EXACTLY the standard side condition
  that distinguishes intuitionistic separation logic (Reynolds' original
  BI-style semantics, and Iris' `Own`) from the classical/exact one:
  in the intuitionistic reading a predicate may not observe the garbage,
  so `P h` must persist as `h` grows.

  So the slogan is not "the leaky heap validates weakening" but

      weakening is available FOR THE PREDICATES THAT ADMIT IT, and `⇓`
      is the free such predicate -- the intuitionisation of `A`.

  which is the same shape as `Affine/Base`'s reading of Rust's `Drop` as
  a trait rather than a structural rule.

  ------------------------------------------------------------------
  §D  WHY THE UNIT LAW MUST FAIL, STRUCTURALLY.

  The refutation is not a coincidence of a chosen counterexample; it is
  forced, and the forcing is one theorem:

      ∗-UpClosed :  (A B : Gr) → UpClosed (A ∗ B)                (§5)

  EVERY separating conjunction is upward closed in the leaky promodel --
  for ARBITRARY `A` and `B`, with no hypothesis at all.  The proof is one
  line: `subIlv-mono` re-indexes the splitting at the bigger heap and the
  two payloads and the disjointness are carried over untouched.  In other
  words `∗` lands in the intuitionistic fragment, always.

  Now suppose `A ∗ emp ⊢ A` for every `A`.  Together with `⇓-unit` in
  the other direction that makes every `A` a retract of `⇓ A`, hence
  every `A` upward closed -- and `emp` is not, since `leakAll` puts the
  empty heap below every heap while `emp` holds only at `[]`.  That is
  `emp-not-UpClosed`, and `no-∗-unitR` is its immediate corollary.  The
  left unit law falls to the same witness (`no-∗-unitL`).

  This also says precisely WHICH direction survives: `A ⊢ A ∗ emp`
  (`⇓-unit`) holds, so `∗` is LAX unital.  Exactly as in `Affine/Base`.

  ------------------------------------------------------------------
  §E  THE SHARPEST CONSEQUENCE:  `⇓ emp ⊣⊢ ⊤G`.

  Every heap has `[]` as a sub-heap, so the upward closure of `emp` is
  everything.  Internally that is `wkUnit : ⊤G ⊢ emp ∗ emp` (§3), which
  is `Affine/Base.wkUnit` verbatim, and `⊤-I` in the other direction.

  This is the known slogan of intuitionistic separation logic in its
  sharpest form: `emp` IS NOT EXPRESSIBLE THERE -- it intuitionises to
  `true`.  A logic that cannot say "the heap is empty" cannot express
  exact footprints, which is why full-blown SL keeps the classical
  reading.  Here that trade is a THEOREM about one constructor rather
  than a design decision about a semantics.

  Dually, `⌈ single l x ⌉` is not upward closed either
  (`↦-not-UpClosed`, §6), and its closure `l ↦ᵢ x = ⇓ ⌈ single l x ⌉` is
  precisely the INTUITIONISTIC POINTS-TO, "the heap contains this cell,
  and possibly more".  So the two standard atoms of intuitionistic SL
  are both literally `⇓` of the corresponding exact atom.

  ------------------------------------------------------------------
  NOT DONE (honestly).  `⇓` lax monoidal (`⇓ A ∗ ⇓ B ⊢ ⇓ (A ∗ B)`)
  needs `#` to be monotone under `⊑` and is not built here.  Nor is
  associativity of `∗` -- `Heap/Emp` declines it for the exact promodel
  for the same reason (a rotation lemma with disjointness bookkeeping),
  and nothing below uses it.

  PRIMITIVE (phase 1): `subIlv-mono`, `⇓→sub`, `sub→⇓`, `wkUnit`,
  `∗-UpClosed`, `alg→up`, `up→alg`.  Each is marked; everything else is a
  composite.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LeakyHeap.Intuitionistic where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Precision using (coeEq)

open import TheoryGrammar.Instances.LeakyHeap.Base public

-- ==================================================================
-- §1  THE SUB-HEAP ORDER.
--
-- `u ⊑ w` is a leaky splitting with an EMPTY right part.  Writing it
-- that way rather than as a separate inductive family is deliberate:
-- the order is not extra structure, it is the promodel's own splitting
-- relation looked at along the unit, which is exactly why the unit law
-- is what it obstructs.
-- ==================================================================

infix 4 _⊑_

_⊑_ : Heap → Heap → Type₀
u ⊑ w = SubIlv u [] w

⊑-refl : (u : Heap) → u ⊑ u
⊑-refl = subIlv-nilR

-- PRIMITIVE (phase 1): a splitting composed with an enlargement of the
-- whole.  This is the single recursion the whole file runs on: it gives
-- transitivity of `⊑`, the monad multiplication, AND the theorem that
-- `∗` is always upward closed.
--
-- `sright` cannot occur in the second argument (its middle slot is a
-- cons, and the second argument's middle is `[]`), which is why the
-- three-clause analysis of the first argument is exhaustive.
subIlv-mono : ∀ {a b u w} → SubIlv a b u → u ⊑ w → SubIlv a b w
subIlv-mono p          snil      = p
subIlv-mono p          (leak q)  = leak   (subIlv-mono p q)
subIlv-mono (sleft p)  (sleft q) = sleft  (subIlv-mono p q)
subIlv-mono (sright p) (sleft q) = sright (subIlv-mono p q)
subIlv-mono (leak p)   (sleft q) = leak   (subIlv-mono p q)

⊑-trans : ∀ {u v w} → u ⊑ v → v ⊑ w → u ⊑ w
⊑-trans = subIlv-mono

-- the bottom of the order: `leakAll`.  In `Ilv` this is refuted --
-- `Ilv [] [] w` forces `w ≡ []` -- and that ONE difference is §3.
⊑-bot : (w : Heap) → [] ⊑ w
⊑-bot = leakAll

-- ==================================================================
-- §2  THE MONAD.
-- ==================================================================

⇓ : Gr → Gr
⇓ A = A ∗ emp

-- PRIMITIVE (phase 1): `⇓ A h ≅ Σ[ u ] (u ⊑ h) × A u`, both maps.  This
-- is the interface to the representation of `⇓`; nothing below unfolds
-- `∗` again.
⇓→sub : (A : Gr) (h : Heap) → (⇓ A) h → Σ[ u ∈ Heap ] (u ⊑ h) × A u
⇓→sub A h ((u , v , s , d) , k) =
  u , subIlv-nilM s (emp-IsNil (k false)) , k true

sub→⇓ : (A : Gr) (h : Heap) → (Σ[ u ∈ Heap ] (u ⊑ h) × A u) → (⇓ A) h
sub→⇓ A h (u , s , x) = ∗-mk A emp h u [] s (#-nil u) x (emp-mk tt)

-- unit: keep everything.  This direction holds for the EXACT promodel
-- too -- it is the half of the unit law that `leak` does not touch.
⇓-unit : (A : Gr) → A ⊢ ⇓ A
⇓-unit A h x = sub→⇓ A h (h , ⊑-refl h , x)

-- multiplication: two successive shrinkings are one shrinking.
⇓-mult : (A : Gr) → ⇓ (⇓ A) ⊢ ⇓ A
⇓-mult A h z =
  sub→⇓ A h ( inner .fst
            , ⊑-trans (inner .snd .fst) (outer .snd .fst)
            , inner .snd .snd )
  where
  outer = ⇓→sub (⇓ A) h z
  inner = ⇓→sub A (outer .fst) (outer .snd .snd)

-- functorial action -- literally the FRAME RULE at `C = emp`.
⇓-map : {A B : Gr} → A ⊢ B → ⇓ A ⊢ ⇓ B
⇓-map {A} {B} f = frame {A} {B} emp f

-- ... and the monad is IDEMPOTENT, so `⇓` is a closure operator.
⇓-idem : (A : Gr) → ⇓ A ⊢ ⇓ (⇓ A)
⇓-idem A = ⇓-unit (⇓ A)

-- ==================================================================
-- §3  WEAKENING, INTERNALLY, AND `⇓ emp ⊣⊢ ⊤G`.
--
-- `Affine/Base.wkUnit` verbatim.  It is the internal `⊗ˢ`-level
-- statement of "everything may be leaked", with NO hypothesis on the
-- heap -- and it is what the exact promodel refutes.
-- ==================================================================

-- PRIMITIVE (phase 1)
wkUnit : ⊤G ⊢ (emp ∗ emp)
wkUnit h _ = ∗-mk emp emp h [] [] (⊑-bot h) tt (emp-mk tt) (emp-mk tt)

-- THE INTUITIONISATION OF `emp` IS `true`.  Both directions; the second
-- is `⊤-I`, so the content is entirely in `wkUnit`.
⊤⊢⇓emp : ⊤G ⊢ ⇓ emp
⊤⊢⇓emp = wkUnit

⇓emp⊢⊤ : ⇓ emp ⊢ ⊤G
⇓emp⊢⊤ = ⊤-I

-- ==================================================================
-- §4  ALGEBRAS = UPWARD-CLOSED = INTUITIONISTIC PREDICATES.
-- ==================================================================

UpClosed : Gr → Type₀
UpClosed A = {u w : Heap} → u ⊑ w → A u → A w

-- "A is INTUITIONISTIC" = A is an algebra for the closure operator = A
-- cannot observe the leaked cells.  A PROPERTY of a predicate, not a
-- rule of the logic -- compare `Affine/Base.Affine`.
Intuitionistic : Gr → Type₀
Intuitionistic A = ⇓ A ⊢ A

-- PRIMITIVE (phase 1): the two directions of the identification.
alg→up : (A : Gr) → Intuitionistic A → UpClosed A
alg→up A alg {u} {w} s x = alg w (sub→⇓ A w (u , s , x))

up→alg : (A : Gr) → UpClosed A → Intuitionistic A
up→alg A up h z = up (⇓→sub A h z .snd .fst) (⇓→sub A h z .snd .snd)

-- the free algebra really is one, and `⊤G` is the terminal one
⇓-Intuitionistic : (A : Gr) → Intuitionistic (⇓ A)
⇓-Intuitionistic A = ⇓-mult A

⊤-Intuitionistic : Intuitionistic ⊤G
⊤-Intuitionistic = ⊤-I

-- ==================================================================
-- §5  THE STRUCTURAL FACT: `∗` ALWAYS LANDS IN THE INTUITIONISTIC
-- FRAGMENT.
--
-- No hypothesis on `A` or `B`.  `subIlv-mono` re-indexes the splitting
-- at the larger heap; the payloads and the disjointness are carried
-- across untouched, because neither mentions the whole.
--
-- THIS is why the unit law cannot hold: `∗` is a closure, and `emp` is
-- not in its image.
-- ==================================================================

-- PRIMITIVE (phase 1)
∗-UpClosed : (A B : Gr) → UpClosed (A ∗ B)
∗-UpClosed A B {u} {w} sub ((a , b , s , d) , k) =
  ∗-mk A B w a b (subIlv-mono s sub) d (k true) (k false)

∗-Intuitionistic : (A B : Gr) → Intuitionistic (A ∗ B)
∗-Intuitionistic A B = up→alg (A ∗ B) (∗-UpClosed A B)

-- ==================================================================
-- §6  ... AND THE REFUTATIONS.  QUESTION 3, ANSWERED: THE UNIT LAW
-- FAILS.
-- ==================================================================

-- `emp` holds only at `[]`, but `[] ⊑ h` for every `h`.  This is the
-- sharpest counterexample available: the unit of the tensor is not its
-- own upward closure, so `∗` is only LAX unital.  Compare
-- `Affine/Base.𝟙-not-⇓-alg`.
emp-not-UpClosed : UpClosed emp → ⊥
emp-not-UpClosed up = emp-IsNil (up {[]} {single 0 v0} (⊑-bot (single 0 v0)) (emp-mk tt))

emp-not-Intuitionistic : Intuitionistic emp → ⊥
emp-not-Intuitionistic alg = emp-not-UpClosed (alg→up emp alg)

-- THE HEADLINE.  The right unit law of `∗` FAILS in the leaky promodel.
-- (It HOLDS exactly -- `Heap/Emp.∗-emp` -- and it holds without
-- disjointness -- `Base.Cell.∗ᶜ-empR`.  It is the one row of the table
-- that separates this column from both others.)
no-∗-unitR : ((A : Gr) → (A ∗ emp) ⊢ A) → ⊥
no-∗-unitR f = emp-not-Intuitionistic (f emp)

-- ... and the left one, on the same witness.
no-∗-unitL : ((A : Gr) → (emp ∗ A) ⊢ A) → ⊥
no-∗-unitL f = emp-not-UpClosed up
  where
  up : UpClosed emp
  up {u} {w} s x =
    f emp w (∗-mk emp emp w [] u (subIlv-mono (subIlv-nilL u) s) tt (emp-mk tt) x)

-- STRUCTURALLY: the unit law would make EVERY predicate upward closed,
-- because `A ⊣⊢ A ∗ emp` and `∗` is always upward closed (§5).  This is
-- the general statement of which `no-∗-unitR` is the instance at `emp`.
unitR→everything-UpClosed :
  ((A : Gr) → (A ∗ emp) ⊢ A) → (A : Gr) → UpClosed A
unitR→everything-UpClosed f A {u} {w} s x =
  f A w (∗-UpClosed A emp s (⇓-unit A u x))

-- ==================================================================
-- §7  THE TWO ATOMS OF INTUITIONISTIC SEPARATION LOGIC ARE `⇓` OF THE
-- EXACT ONES.
--
-- `emp` intuitionises to `⊤G` (§3), and the exact points-to
-- intuitionises to the "contains this cell, possibly more" points-to.
-- Neither exact atom is upward closed, and that is the whole difference
-- between the two logics.
-- ==================================================================

infix 9 _↦_ _↦ᵢ_

-- the EXACT points-to: the heap is EXACTLY this one cell
_↦_ : Loc → Val → Gr
l ↦ x = ⌈ single l x ⌉

-- the INTUITIONISTIC points-to: the heap CONTAINS this cell
_↦ᵢ_ : Loc → Val → Gr
l ↦ᵢ x = ⇓ (l ↦ x)

↦⊢↦ᵢ : (l : Loc) (x : Val) → (l ↦ x) ⊢ (l ↦ᵢ x)
↦⊢↦ᵢ l x = ⇓-unit (l ↦ x)

-- ... and the inclusion is STRICT: the exact atom is not upward closed.
-- Witness: put one more cell on top and compare cell counts.
private
  s0 : Heap
  s0 = single 0 v0

  big : Heap
  big = (1 , v1) ∷ s0

-- `⌈ a ⌉ m` is `m Eq.≡ a`, so upward closure at `s0 ⊑ big` would say
-- `big Eq.≡ s0`; `coeEq` moves the cell count across it and `1 ≡ 2` is
-- refuted.  `coeEq` reduces on `Eq.refl`, so nothing here goes inert.
↦-not-UpClosed : UpClosed (0 ↦ v0) → ⊥
↦-not-UpClosed up =
  znots (injSuc (coeEq (λ z → length z ≡ 2) (up {s0} {big} (leak (⊑-refl s0)) Eq.refl) refl))

↦-not-Intuitionistic : Intuitionistic (0 ↦ v0) → ⊥
↦-not-Intuitionistic alg = ↦-not-UpClosed (alg→up (0 ↦ v0) alg)

-- ... whereas the intuitionistic one is, being a `⇓`.
↦ᵢ-Intuitionistic : (l : Loc) (x : Val) → Intuitionistic (l ↦ᵢ x)
↦ᵢ-Intuitionistic l x = ⇓-Intuitionistic (l ↦ x)
