{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  JSON, ACROSS TWO THEORIES JOINED BY SORT.

  The claim this file is here to make good on:

      {"id":7,"tags":[1,"x"]}   and   {"tags":[1,"x"],"id":7}

  are the SAME parse, and

      {"id":7,"tags":["x",1]}

  is not -- with no normalisation pass anywhere.  Ordinary parsers
  produce an ordered list of members and canonicalise afterwards; the
  canonicalisation is a separate program with a separate correctness
  proof.  Here it is the TENSOR OF THE THEORY, and there is nothing to
  prove because there is nothing to normalise.

  ==================================================================
  THREE SORTS, TWO MULTIPLICATIVES.

  `TheoryTy` is a family over `carrier s`, so nothing stops one
  signature from having several sorts with DIFFERENT multiplicative
  structure.  That is what this instance is:

      sort   carrier          its ⊗            order-sensitive?
      ----   -------          ---              ----------------
      obj    List Member      `uni`, INTERLEAVING     no
      arr    List Val         `cat`, CONCATENATION    yes
      val    Val              (no binary op)          --

  `⊗ˢ uni` splits a bag of members into two sub-bags in every possible
  way -- `Ilv`, the same relation `Instances.Bags` uses -- so a grammar
  for an object as a bag of members accepts every key order by
  construction.  `⊗ˢ cat` splits a list of values at a cut -- `Cat3`,
  the same relation `Instances.Strings` uses -- so an array grammar is
  order-sensitive by construction.

  The two are JOINED BY SORT, and the joins are the unary operations:

      objOf : obj → val     "this value is an object"
      arrOf : arr → val     "this value is an array"
      mem k : val → obj     "this bag is the single member  k : v"
      one   : val → arr     "this list is the single element v"

  So one document descends through both theories, alternating, and the
  guarded recursion (`deg`) crosses the sorts freely because
  `GradedFib.deg` is already indexed by the sort.  This is what
  `ChangeOfTheory`'s header says CANNOT be done by translation --
  abelianisation does not reflect splittings, so string grammars do not
  reinterpret as multiset grammars -- and it is why the two theories are
  joined by a SORT rather than by a signature morphism.

  ==================================================================
  EVERY OPERATION HAS ARITY `Bool`.

  The four joins above are unary, and a unary operation would make the
  arity `Unit`, which forces a second copy of every arity-indexed
  combinator (`decΠBool` has no `Unit` twin).  So each of them is given
  a DUMMY second slot, whose part is the empty carrier and whose grammar
  is `⌜ ⊤G ⌝`.  A constant former has no positions, so the dummy
  contributes nothing to guardedness, and `Proper` at these operations
  is `Unit` -- both slots strictly shrink, always, because the join
  itself costs a `suc` of degree.  The gain is that `decΠBool`, `boolAr`
  and `⊗at` are used at every operation without a second family.

  ==================================================================
  THE GRAMMAR IS A SCHEMA, and that is where key order bites.

  A grammar that accepted any bag of members would make the reordering
  test vacuous.  The description below is the record type

      Rec  =  { id : Num , tags : [Num, Txt] }

  -- exactly two members, with fixed keys and fixed value types, in ANY
  order; and an array of exactly two elements, a number then a string,
  in THAT order.  So the two tests are:

      key order      irrelevant   -- `uni` is commutative
      element order  relevant     -- `cat` is not

  and one document exhibits both.

  ==================================================================
  WHAT IS PHASE 1 HERE.

  Everything down to `jsonGraded` is the substrate: signature,
  splittings as output-indexed data, the grading, the enumeration of
  splittings.  Then the PRIMITIVES, each named and `⊢`-typed where a
  `⊢` exists:

      probeNum / probeTxt   the lexical table  (`Spans.Examples.termProbe`)
      probe-NEobj / -NEarr  the resource tests
      neO / neA             the one bridge from the internal resource
                            predicate to the grading
      neOfSh                `neOf` at the level of SHAPES

  and from `decRule` down every line is a composite of `∘g`, `&ᴰ-I`,
  `&ᴰ-E`, `dec-map`, `dec-&ᴰ`, `dec-⊗▷` and `resourceOf`.
-}
module TheoryGrammar.Instances.Bags.JSON where

open import Cubical.Foundations.Prelude
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
open import TheoryGrammar.Enumerable
open import TheoryGrammar.View
open import TheoryGrammar.Decidable.Tensor
open import TheoryGrammar.Decidable.Enumerated
open import TheoryGrammar.Decidable.Guarded

-- THE SIGNATURE.

data JSort : Type₀ where
  val obj arr : JSort

-- A fixed, finite key alphabet.  Keys index the `mem` operation, so
-- making them finite keeps `KEq` a decidable Unit/⊥ predicate and keeps
-- the splitting enumeration free of any propositional equality.
data Key : Type₀ where
  kId kTags kName : Key

KEq : Key → Key → Type₀
KEq kId   kId   = Unit
KEq kTags kTags = Unit
KEq kName kName = Unit
KEq _     _     = ⊥

data JOp : Type₀ where
  uni   : JOp          -- obj ⊗ obj → obj    INTERLEAVING (commutative)
  cat   : JOp          -- arr ⊗ arr → arr    CONCATENATION (ordered)
  objOf : JOp          -- obj → val          a value that is an object
  arrOf : JOp          -- arr → val          a value that is an array
  mem   : Key → JOp    -- val → obj          the singleton member  k : v
  one   : JOp          -- val → arr          the singleton element [v]

-- Every operation has arity `Bool`; see the header.  For the four
-- joins, slot `false` is the DUMMY.
JAr : JOp → Type₀
JAr _ = Bool

JSortOf : (o : JOp) → JAr o → JSort
JSortOf uni     _     = obj
JSortOf cat     _     = arr
JSortOf objOf   _     = obj
JSortOf arrOf   _     = arr
JSortOf (mem k) true  = val
JSortOf (mem k) false = obj
JSortOf one     true  = val
JSortOf one     false = arr

JResult : JOp → JSort
JResult uni     = obj
JResult cat     = arr
JResult objOf   = val
JResult arrOf   = val
JResult (mem k) = obj
JResult one     = arr

jsonSig : SortedSig JSort ℓ-zero ℓ-zero
jsonSig .ops        = JOp
jsonSig .arities    = JAr
jsonSig .sortOf     = JSortOf
jsonSig .resultSort = JResult

-- THE CARRIERS.  One document, three sorts of piece.

data Val : Type₀ where
  num  : ℕ → Val                    -- a number
  txt  : ℕ → Val                    -- a string, as a code
  arrV : List Val → Val             -- an array   -- ORDERED
  objV : List (Key × Val) → Val     -- an object  -- a BAG

Member : Type₀
Member = Key × Val

JCar : JSort → Type₀
JCar val = Val
JCar obj = List Member
JCar arr = List Val

-- THE SPLITTINGS, as data indexed by the output.

-- the COMMUTATIVE one: a bag of members splits into two sub-bags
data Ilv : List Member → List Member → List Member → Type₀ where
  nilI   : Ilv [] [] []
  leftI  : ∀ {x u v w} → Ilv u v w → Ilv (x ∷ u) v (x ∷ w)
  rightI : ∀ {x u v w} → Ilv u v w → Ilv u (x ∷ v) (x ∷ w)

-- the ORDERED one: a list of values cuts into a prefix and a suffix
data Cat3 : List Val → List Val → List Val → Type₀ where
  nilC  : ∀ {v} → Cat3 [] v v
  consC : ∀ {x u v w} → Cat3 u v w → Cat3 (x ∷ u) v (x ∷ w)

-- ... and the joins, each a RECURSIVE predicate (Unit or ⊥), so that
-- `parts` computes and the enumeration below is a one-liner.
IsObj : Val → Type₀
IsObj (objV _) = Unit
IsObj _        = ⊥

IsArr : Val → Type₀
IsArr (arrV _) = Unit
IsArr _        = ⊥

IsMem : Key → List Member → Type₀
IsMem k []             = ⊥
IsMem k ((k' , _) ∷ []) = KEq k' k
IsMem k (_ ∷ _ ∷ _)    = ⊥

IsSingle : List Val → Type₀
IsSingle []          = ⊥
IsSingle (_ ∷ [])    = Unit
IsSingle (_ ∷ _ ∷ _) = ⊥

JSplit : (o : JOp) → JCar (JResult o) → Type₀
JSplit uni     w = Σ[ u ∈ List Member ] Σ[ v ∈ List Member ] Ilv u v w
JSplit cat     l = Σ[ u ∈ List Val ] Σ[ v ∈ List Val ] Cat3 u v l
JSplit objOf   v = IsObj v
JSplit arrOf   v = IsArr v
JSplit (mem k) b = IsMem k b
JSplit one     l = IsSingle l

JParts : (o : JOp) (m : JCar (JResult o)) → JSplit o m
       → (a : JAr o) → JCar (JSortOf o a)
JParts uni     w         (u , v , _) true  = u
JParts uni     w         (u , v , _) false = v
JParts cat     l         (u , v , _) true  = u
JParts cat     l         (u , v , _) false = v
JParts objOf   (num _)   ()
JParts objOf   (txt _)   ()
JParts objOf   (arrV _)  ()
JParts objOf   (objV b)  tt          true  = b
JParts objOf   (objV b)  tt          false = []
JParts arrOf   (num _)   ()
JParts arrOf   (txt _)   ()
JParts arrOf   (objV _)  ()
JParts arrOf   (arrV l)  tt          true  = l
JParts arrOf   (arrV l)  tt          false = []
JParts (mem k) []        ()
JParts (mem k) ((k' , v) ∷ [])       sp    true  = v
JParts (mem k) ((k' , v) ∷ [])       sp    false = []
JParts (mem k) (_ ∷ _ ∷ _)           ()
JParts one     []        ()
JParts one     (v ∷ [])  tt          true  = v
JParts one     (v ∷ [])  tt          false = []
JParts one     (_ ∷ _ ∷ _)           ()

jsonFib : Fibered jsonSig ℓ-zero ℓ-zero
jsonFib .carrier = JCar
jsonFib .Split   = JSplit
jsonFib .parts   = JParts

-- the connectives, the decision layer, the semantic actions, the views
open DecFib jsonFib public
open Views  jsonFib public

-- The two multiplicatives, named.

infixr 21 _⊗ᵒ_ _⊗ᵃ_

-- the COMMUTATIVE tensor: "this bag splits into an A-bag and a B-bag"
_⊗ᵒ_ : TheoryTy ℓ-zero obj → TheoryTy ℓ-zero obj → TheoryTy ℓ-zero obj
A ⊗ᵒ B = ⊗ˢ uni (λ b → if b then A else B)

-- the ORDERED tensor: "this list cuts into an A-list then a B-list"
_⊗ᵃ_ : TheoryTy ℓ-zero arr → TheoryTy ℓ-zero arr → TheoryTy ℓ-zero arr
A ⊗ᵃ B = ⊗ˢ cat (λ b → if b then A else B)

-- THE CLAIM, AS A TERM. "Key order does not matter" is not an observation
-- about the tests: it is COMMUTATIVITY of the object sort's tensor, and it
-- is a map of the calculus, discharged by swapping an interleaving.

ilvSwap : ∀ {u v w} → Ilv u v w → Ilv v u w
ilvSwap nilI       = nilI
ilvSwap (leftI s)  = rightI (ilvSwap s)
ilvSwap (rightI s) = leftI  (ilvSwap s)

⊗ᵒ-comm : {A B : TheoryTy ℓ-zero obj} → (A ⊗ᵒ B) ⊢ (B ⊗ᵒ A)
⊗ᵒ-comm w ((u , v , s) , h) =
  (v , u , ilvSwap s) , λ { true → h false ; false → h true }

-- The constant former's level coercion (`⟦ ⌜ B ⌝ ⟧c A m = Lift _ (B m)`).

-- THE GRADING.  One degree function per sort, and the joins each cost
-- a `suc` -- which is exactly why the four unary operations are
-- strictly decreasing with no side condition at all.

degV : Val → ℕ
degA : List Val → ℕ
degO : List Member → ℕ

degV (num _)  = 1
degV (txt _)  = 1
degV (arrV l) = suc (degA l)
degV (objV b) = suc (degO b)

degA []      = 0
degA (v ∷ l) = suc (degA l + degV v)

degO []            = 0
degO ((k , v) ∷ b) = suc (degO b + degV v)

jdeg : (s : JSort) → JCar s → ℕ
jdeg val = degV
jdeg obj = degO
jdeg arr = degA

-- Interleaving never grows a sub-bag, and shrinks it strictly once the
-- COMPLEMENT is non-empty.  Same four lemmas as `Bags.Graded`, with the
-- weighted degree in place of `length`.
degO-L : ∀ {u v w} → Ilv u v w → degO u ≤ degO w
degO-L nilI       = ≤-refl
degO-L (leftI s)  = suc-≤-suc (≤-+k (degO-L s))
degO-L (rightI s) = ≤-suc (≤-trans (degO-L s) ≤SumLeft)

degO-R : ∀ {u v w} → Ilv u v w → degO v ≤ degO w
degO-R nilI       = ≤-refl
degO-R (leftI s)  = ≤-suc (≤-trans (degO-R s) ≤SumLeft)
degO-R (rightI s) = suc-≤-suc (≤-+k (degO-R s))

degO-L< : ∀ {u v w} → Ilv u v w → 0 < degO v → degO u < degO w
degO-L< nilI       pr = E.rec (¬-<-zero pr)
degO-L< (leftI s)  pr = suc-≤-suc (≤-+k (degO-L< s pr))
degO-L< (rightI s) pr = suc-≤-suc (≤-trans (degO-L s) ≤SumLeft)

degO-R< : ∀ {u v w} → Ilv u v w → 0 < degO u → degO v < degO w
degO-R< nilI       pr = E.rec (¬-<-zero pr)
degO-R< (leftI s)  pr = suc-≤-suc (≤-trans (degO-R s) ≤SumLeft)
degO-R< (rightI s) pr = suc-≤-suc (≤-+k (degO-R< s pr))

-- ... and the same for a CUT of a list of values.
degA-L : ∀ {u v l} → Cat3 u v l → degA u ≤ degA l
degA-L nilC      = zero-≤
degA-L (consC s) = suc-≤-suc (≤-+k (degA-L s))

degA-R : ∀ {u v l} → Cat3 u v l → degA v ≤ degA l
degA-R nilC      = ≤-refl
degA-R (consC s) = ≤-suc (≤-trans (degA-R s) ≤SumLeft)

degA-L< : ∀ {u v l} → Cat3 u v l → 0 < degA v → degA u < degA l
degA-L< nilC      pr = pr
degA-L< (consC s) pr = suc-≤-suc (≤-+k (degA-L< s pr))

degA-R< : ∀ {u v l} → Cat3 u v l → 0 < degA u → degA v < degA l
degA-R< nilC      pr = E.rec (¬-<-zero pr)
degA-R< (consC s) pr = suc-≤-suc (≤-trans (degA-R s) ≤SumLeft)

-- THE RESOURCE PREDICATES, internally.  Built from `⌈_⌉`, the tensor,
-- `⊕ᴰ` and `⊤` only -- no degree -- exactly as `Bags.Graded.NonTrivial`
-- and `Spans.Graded.NonEmpty` are.

NEobj : TheoryTy ℓ-zero obj
NEobj = ⊕ᴰ Member (λ mm → ⌈ mm ∷ [] ⌉ ⊗ᵒ ⊤G)

NEarr : TheoryTy ℓ-zero arr
NEarr = ⊕ᴰ Val (λ v → ⌈ v ∷ [] ⌉ ⊗ᵃ ⊤G)

-- PRIMITIVE (phase 1).  The ONE bridge from the internal predicate to
-- the grading, confined to where the grading is defined.
neO : {b : List Member} → NEobj b → 0 < degO b
neO {b} (mm , (u , v , ilv) , h) = go (h true) ilv
  where go : u Eq.≡ (mm ∷ []) → Ilv u v b → 0 < degO b
        go Eq.refl s = ≤-trans (suc-≤-suc zero-≤) (degO-L s)

neA : {l : List Val} → NEarr l → 0 < degA l
neA {l} (x , (u , v , c) , h) = go (h true) c
  where go : u Eq.≡ (x ∷ []) → Cat3 u v l → 0 < degA l
        go Eq.refl s = ≤-trans (suc-≤-suc zero-≤) (degA-L s)

-- the resource, as a family over the SORTS.  `val` has no binary
-- operation, so nothing there is ever asked to be a proper part.
NEres : (s : JSort) → TheoryTy ℓ-zero s
NEres val = ⊤G
NEres obj = NEobj
NEres arr = NEarr

-- Properness, and the graded `Fibered`. For the two binary operations
-- properness of a slot IS non-triviality of its COMPLEMENT -- stated
-- through `JParts` so that it reduces at a variable splitting, exactly as
-- `Spans.Graded.SpanProper` does.

JProper : (o : JOp) (m : JCar (JResult o)) → JSplit o m → JAr o → Type₀
JProper uni     m sp a = NEobj (JParts uni m sp (not a))
JProper cat     m sp a = NEarr (JParts cat m sp (not a))
JProper objOf   m sp a = Unit
JProper arrOf   m sp a = Unit
JProper (mem k) m sp a = Unit
JProper one     m sp a = Unit

jdeg≤ : (o : JOp) (m : JCar (JResult o)) (sp : JSplit o m) (a : JAr o)
      → jdeg _ (JParts o m sp a) ≤ jdeg _ m
jdeg≤ uni     w        (u , v , s) true  = degO-L s
jdeg≤ uni     w        (u , v , s) false = degO-R s
jdeg≤ cat     l        (u , v , s) true  = degA-L s
jdeg≤ cat     l        (u , v , s) false = degA-R s
jdeg≤ objOf   (num _)  ()
jdeg≤ objOf   (txt _)  ()
jdeg≤ objOf   (arrV _) ()
jdeg≤ objOf   (objV b) tt          true  = ≤-suc ≤-refl
jdeg≤ objOf   (objV b) tt          false = zero-≤
jdeg≤ arrOf   (num _)  ()
jdeg≤ arrOf   (txt _)  ()
jdeg≤ arrOf   (objV _) ()
jdeg≤ arrOf   (arrV l) tt          true  = ≤-suc ≤-refl
jdeg≤ arrOf   (arrV l) tt          false = zero-≤
jdeg≤ (mem k) []       ()
jdeg≤ (mem k) ((k' , v) ∷ [])      sp    true  = ≤-suc ≤-refl
jdeg≤ (mem k) ((k' , v) ∷ [])      sp    false = zero-≤
jdeg≤ (mem k) (_ ∷ _ ∷ _)          ()
jdeg≤ one     []       ()
jdeg≤ one     (v ∷ []) tt          true  = ≤-suc ≤-refl
jdeg≤ one     (v ∷ []) tt          false = zero-≤
jdeg≤ one     (_ ∷ _ ∷ _)          ()

jdeg< : (o : JOp) (m : JCar (JResult o)) (sp : JSplit o m) (a : JAr o)
      → JProper o m sp a → jdeg _ (JParts o m sp a) < jdeg _ m
jdeg< uni     w        (u , v , s) true  pr = degO-L< s (neO pr)
jdeg< uni     w        (u , v , s) false pr = degO-R< s (neO pr)
jdeg< cat     l        (u , v , s) true  pr = degA-L< s (neA pr)
jdeg< cat     l        (u , v , s) false pr = degA-R< s (neA pr)
jdeg< objOf   (num _)  ()
jdeg< objOf   (txt _)  ()
jdeg< objOf   (arrV _) ()
jdeg< objOf   (objV b) tt          true  _ = ≤-refl
jdeg< objOf   (objV b) tt          false _ = suc-≤-suc zero-≤
jdeg< arrOf   (num _)  ()
jdeg< arrOf   (txt _)  ()
jdeg< arrOf   (objV _) ()
jdeg< arrOf   (arrV l) tt          true  _ = ≤-refl
jdeg< arrOf   (arrV l) tt          false _ = suc-≤-suc zero-≤
jdeg< (mem k) []       ()
jdeg< (mem k) ((k' , v) ∷ [])      sp    true  _ = ≤-refl
jdeg< (mem k) ((k' , v) ∷ [])      sp    false _ = suc-≤-suc zero-≤
jdeg< (mem k) (_ ∷ _ ∷ _)          ()
jdeg< one     []       ()
jdeg< one     (v ∷ []) tt          true  _ = ≤-refl
jdeg< one     (v ∷ []) tt          false _ = suc-≤-suc zero-≤
jdeg< one     (_ ∷ _ ∷ _)          ()

jsonGraded : GradedFib jsonSig ℓ-zero ℓ-zero
jsonGraded .fib    = jsonFib
jsonGraded .deg    = jdeg
jsonGraded .Proper = JProper
jsonGraded .deg≤   = jdeg≤
jsonGraded .deg<   = jdeg<

-- THE RESOURCE LAW, one per binary operation: "if every slot of a
-- splitting is non-trivial then every slot is a proper part".
uniProper : (m : List Member) (sp : JSplit uni m)
          → ((a : Bool) → NEres obj (JParts uni m sp a))
          → (a : Bool) → JProper uni m sp a
uniProper m sp h a = h (not a)

catProper : (m : List Val) (sp : JSplit cat m)
          → ((a : Bool) → NEres arr (JParts cat m sp a))
          → (a : Bool) → JProper cat m sp a
catProper m sp h a = h (not a)

boolAr : List Bool
boolAr = true ∷ false ∷ []

boolArComplete : (a : Bool) → a ∈L boolAr
boolArComplete true  = here
boolArComplete false = there here

-- THE SPLITTINGS ARE FINITELY ENUMERABLE. The residual obligation, and the
-- one place the cost of commutativity is visible: a bag of `n` members has
-- `2ⁿ` interleavings, against a list's `n+1` cuts.

allIlv : (w : List Member)
       → List (Σ[ u ∈ List Member ] Σ[ v ∈ List Member ] Ilv u v w)
allIlv []      = ([] , [] , nilI) ∷ []
allIlv (x ∷ w) =
     map (λ { (u , v , s) → (x ∷ u , v , leftI s) })  (allIlv w)
  ++ map (λ { (u , v , s) → (u , x ∷ v , rightI s) }) (allIlv w)

allIlvComplete : {u v w : List Member} (s : Ilv u v w) → (u , v , s) ∈L allIlv w
allIlvComplete nilI       = here
allIlvComplete (leftI s)  = ∈++ˡ (∈map _ (allIlvComplete s))
allIlvComplete (rightI s) = ∈++ʳ _ (∈map _ (allIlvComplete s))

allCat : (l : List Val) → List (Σ[ u ∈ List Val ] Σ[ v ∈ List Val ] Cat3 u v l)
allCat []      = ([] , [] , nilC) ∷ []
allCat (x ∷ l) =
  ([] , x ∷ l , nilC) ∷ map (λ { (u , v , s) → (x ∷ u , v , consC s) }) (allCat l)

allCatComplete : {u v l : List Val} (s : Cat3 u v l) → (u , v , s) ∈L allCat l
allCatComplete {v = []}    nilC = here
allCatComplete {v = _ ∷ _} nilC = here
allCatComplete (consC s)        = there (∈map _ (allCatComplete s))

kIs : (k' k : Key) → List (KEq k' k)
kIs kId   kId   = tt ∷ []
kIs kTags kTags = tt ∷ []
kIs kName kName = tt ∷ []
kIs kId   kTags = []
kIs kId   kName = []
kIs kTags kId   = []
kIs kTags kName = []
kIs kName kId   = []
kIs kName kTags = []

kIsComplete : (k' k : Key) (e : KEq k' k) → e ∈L kIs k' k
kIsComplete kId   kId   tt = here
kIsComplete kTags kTags tt = here
kIsComplete kName kName tt = here
kIsComplete kId   kTags ()
kIsComplete kId   kName ()
kIsComplete kTags kId   ()
kIsComplete kTags kName ()
kIsComplete kName kId   ()
kIsComplete kName kTags ()

jEnum : (o : JOp) (m : JCar (JResult o)) → List (JSplit o m)
jEnum uni     w        = allIlv w
jEnum cat     l        = allCat l
jEnum objOf   (num _)  = []
jEnum objOf   (txt _)  = []
jEnum objOf   (arrV _) = []
jEnum objOf   (objV _) = tt ∷ []
jEnum arrOf   (num _)  = []
jEnum arrOf   (txt _)  = []
jEnum arrOf   (objV _) = []
jEnum arrOf   (arrV _) = tt ∷ []
jEnum (mem k) []       = []
jEnum (mem k) ((k' , v) ∷ []) = kIs k' k
jEnum (mem k) (_ ∷ _ ∷ _)     = []
jEnum one     []       = []
jEnum one     (_ ∷ []) = tt ∷ []
jEnum one     (_ ∷ _ ∷ _)     = []

jEnumComplete : (o : JOp) (m : JCar (JResult o)) (sp : JSplit o m)
             → sp ∈L jEnum o m
jEnumComplete uni     w        (u , v , s) = allIlvComplete s
jEnumComplete cat     l        (u , v , s) = allCatComplete s
jEnumComplete objOf   (num _)  ()
jEnumComplete objOf   (txt _)  ()
jEnumComplete objOf   (arrV _) ()
jEnumComplete objOf   (objV _) tt = here
jEnumComplete arrOf   (num _)  ()
jEnumComplete arrOf   (txt _)  ()
jEnumComplete arrOf   (objV _) ()
jEnumComplete arrOf   (arrV _) tt = here
jEnumComplete (mem k) []       ()
jEnumComplete (mem k) ((k' , v) ∷ []) e = kIsComplete k' k e
jEnumComplete (mem k) (_ ∷ _ ∷ _)     ()
jEnumComplete one     []       ()
jEnumComplete one     (_ ∷ []) tt = here
jEnumComplete one     (_ ∷ _ ∷ _)     ()

-- THE PROBES -- the file's primitives, each with an INTERNAL type.

-- PRIMITIVE (phase 1).  THE LEXICAL TABLE: is this value a number?  a
-- string?  Matching the carrier is exactly what building a `Probe` is
-- for; its TYPE is internal, so nothing downstream sees a `Val`.
NumG : TheoryTy ℓ-zero val
NumG = ⊕ᴰ ℕ (λ n → ⌈ num n ⌉)

TxtG : TheoryTy ℓ-zero val
TxtG = ⊕ᴰ ℕ (λ n → ⌈ txt n ⌉)

probeNum : Probe NumG
probeNum (num n)  _ = dec-yes NumG (num n) (n , Eq.refl)
probeNum (txt n)  _ = dec-no  NumG (txt n)  λ { (m , ()) }
probeNum (arrV l) _ = dec-no  NumG (arrV l) λ { (m , ()) }
probeNum (objV b) _ = dec-no  NumG (objV b) λ { (m , ()) }

probeTxt : Probe TxtG
probeTxt (txt n)  _ = dec-yes TxtG (txt n) (n , Eq.refl)
probeTxt (num n)  _ = dec-no  TxtG (num n)  λ { (m , ()) }
probeTxt (arrV l) _ = dec-no  TxtG (arrV l) λ { (m , ()) }
probeTxt (objV b) _ = dec-no  TxtG (objV b) λ { (m , ()) }

-- PRIMITIVE (phase 1).  The resource tests.  `mkNE` for bags is
-- `leftI` of the all-right interleaving; for lists it is `consC nilC`.
ilvNilL : (v : List Member) → Ilv [] v v
ilvNilL []      = nilI
ilvNilL (x ∷ v) = rightI (ilvNilL v)

probe-NEobj : Probe NEobj
probe-NEobj []       _ = dec-no NEobj [] λ ne → E.rec (¬-<-zero (neO ne))
probe-NEobj (x ∷ b)  _ =
  dec-yes NEobj (x ∷ b)
    (x , (x ∷ [] , b , leftI (ilvNilL b)) , λ { true → Eq.refl ; false → tt })

probe-NEarr : Probe NEarr
probe-NEarr []       _ = dec-no NEarr [] λ ne → E.rec (¬-<-zero (neA ne))
probe-NEarr (x ∷ l)  _ =
  dec-yes NEarr (x ∷ l)
    (x , (x ∷ [] , l , consC nilC) , λ { true → Eq.refl ; false → tt })

probeR : (s : JSort) → ⊤G {s} ⊢ Dec⟨ NEres s ⟩
probeR val = dec-⊤
probeR obj = probe-NEobj
probeR arr = probe-NEarr

-- THE DESCRIPTION. The schema is Rec = { id : Num , tags : Tags } -- a BAG
-- of members Tags = [ Num , Txt ] -- an ORDERED list and the nonterminals
-- are indexed by their SORT, which is what makes the chart below a family
-- over the sorts rather than over one type.

data ValNT : Type₀ where
  ntNum ntTxt ntRec ntRec3 ntTags : ValNT

data ObjNT : Type₀ where
  ntRecBody ntRec3Body ntTagsName ntIdMem ntTagsMem ntNameMem : ObjNT

data ArrNT : Type₀ where
  ntTagsBody ntNumElem ntTxtElem : ArrNT

V : JSort → Type₀
V val = ValNT
V obj = ObjNT
V arr = ArrNT

-- X, indexed BY THE SORT.  `xs = fst`, so the restriction of a
-- nonterminal family to a sort is DEFINITIONALLY `V s` -- which is what
-- lets the chart be a `&ᴰ (V s)` with no transport anywhere.
NT : Type₀
NT = Σ[ s ∈ JSort ] V s

module G = Guard jsonGraded ℓ-zero NT fst

-- a recursive occurrence together with a proof its part is non-trivial;
-- the sibling's copy of that proof is what makes THIS slot proper
NEslot : (s : JSort) (P : V s) → Bool → G.Functor s
NEslot s P true  = G.Var (s , P)
NEslot s P false = G.⌜ NEres s ⌝

Slot : (s : JSort) → V s → G.Functor s
Slot s P = G.&e Bool (NEslot s P)

-- the slots of the two BINARY rules
uniSlots : (P Q : ObjNT) (a : JAr uni) → G.Functor (JSortOf uni a)
uniSlots P Q true  = Slot obj P
uniSlots P Q false = Slot obj Q

catSlots : (P Q : ArrNT) (a : JAr cat) → G.Functor (JSortOf cat a)
catSlots P Q true  = Slot arr P
catSlots P Q false = Slot arr Q

-- ... and of the four JOINS, whose second slot is the dummy
objOfSlots : (P : ObjNT) (a : JAr objOf) → G.Functor (JSortOf objOf a)
objOfSlots P true  = G.Var (obj , P)
objOfSlots P false = G.⌜ ⊤G {obj} ⌝

arrOfSlots : (P : ArrNT) (a : JAr arrOf) → G.Functor (JSortOf arrOf a)
arrOfSlots P true  = G.Var (arr , P)
arrOfSlots P false = G.⌜ ⊤G {arr} ⌝

memSlots : (k : Key) (P : ValNT) (a : JAr (mem k)) → G.Functor (JSortOf (mem k) a)
memSlots k P true  = G.Var (val , P)
memSlots k P false = G.⌜ ⊤G {obj} ⌝

oneSlots : (P : ValNT) (a : JAr one) → G.Functor (JSortOf one a)
oneSlots P true  = G.Var (val , P)
oneSlots P false = G.⌜ ⊤G {arr} ⌝

-- THE GRAMMAR.  Each nonterminal has exactly one production, so there
-- is no `⊕e` layer and no rule search: the schema is deterministic and
-- the only search is over SPLITTINGS.
JF : (x : NT) → G.Functor (fst x)
JF (val , ntNum)      = G.⌜ NumG ⌝
JF (val , ntTxt)      = G.⌜ TxtG ⌝
JF (val , ntRec)      = G.⊗e objOf (objOfSlots ntRecBody)
JF (val , ntTags)     = G.⊗e arrOf (arrOfSlots ntTagsBody)
JF (obj , ntRecBody)  = G.⊗e uni (uniSlots ntIdMem ntTagsMem)
JF (obj , ntIdMem)    = G.⊗e (mem kId)   (memSlots kId   ntNum)
JF (obj , ntTagsMem)  = G.⊗e (mem kTags) (memSlots kTags ntTags)
-- ... and the same schema with a THIRD member.
JF (val , ntRec3)     = G.⊗e objOf (objOfSlots ntRec3Body)
JF (obj , ntRec3Body) = G.⊗e uni (uniSlots ntIdMem ntTagsName)
JF (obj , ntTagsName) = G.⊗e uni (uniSlots ntTagsMem ntNameMem)
JF (obj , ntNameMem)  = G.⊗e (mem kName)  (memSlots kName  ntTxt)
JF (arr , ntTagsBody) = G.⊗e cat (catSlots ntNumElem ntTxtElem)
JF (arr , ntNumElem)  = G.⊗e one (oneSlots ntNum)
JF (arr , ntTxtElem)  = G.⊗e one (oneSlots ntTxt)

Der : G.Ix → Type₀
Der = G.μ JF

-- THE PARSE TREES, as a grammar at the nonterminal's own sort
DerivAt : (x : NT) → TheoryTy ℓ-zero (fst x)
DerivAt x m = G.μ JF (x , m)

LayerAt : (x : NT) → TheoryTy ℓ-zero (fst x)
LayerAt x = G.⟦ JF x ⟧c Der

SlotG : (s : JSort) (P : V s) → TheoryTy ℓ-zero s
SlotG s P = G.⟦ Slot s P ⟧c Der

-- the fixed point, as maps of the calculus.
unrollD : (x : NT) → DerivAt x ⊢ LayerAt x
unrollD = G.unrollg JF

rollD : (x : NT) → LayerAt x ⊢ DerivAt x
rollD = G.rollg JF

-- THE RESOURCE CERTIFICATE A SLOT CARRIES -- a term.
neOf : (s : JSort) (P : V s) → SlotG s P ⊢ NEres s
neOf s P = lowerg ∘g &ᴰ-E Bool {B = λ b → G.⟦ NEslot s P b ⟧c Der} false

derOf : (s : JSort) (P : V s) → SlotG s P ⊢ DerivAt (s , P)
derOf s P = &ᴰ-E Bool {B = λ b → G.⟦ NEslot s P b ⟧c Der} true

-- GUARDEDNESS: the chart is filled by increasing degree, and the recursion
-- crosses the sorts.

-- PRIMITIVE (phase 1): `neOf` at the level of SHAPES, which is where
-- guardedness lives.  The only place a `Sh` is looked at.
neOfSh : (s : JSort) (P : V s) (m : JCar s) → G.Sh (Slot s P) m → NEres s m
neOfSh s P m sh = lower (sh false)

≤NEslot : (s : JSort) (P : V s) (b : Bool) → G.Guarded≤ (NEslot s P b)
≤NEslot s P true  = G.≤Var (s , P)
≤NEslot s P false = G.≤⌜⌝ (NEres s)

≤Slot : (s : JSort) (P : V s) → G.Guarded≤ (Slot s P)
≤Slot s P = G.≤&e Bool (NEslot s P) (≤NEslot s P)

uniGuarded : (P Q : ObjNT) → G.Guarded (G.⊗e uni (uniSlots P Q))
uniGuarded P Q =
  G.<⊗e uni (uniSlots P Q) (λ { true → ≤Slot obj P ; false → ≤Slot obj Q }) pr
  where
    pr : (m : List Member) (sp : JSplit uni m)
         (sh : (a : Bool) → G.Sh (uniSlots P Q a) (JParts uni m sp a))
         (a : Bool) → G.Pos (uniSlots P Q a) _ (sh a) → JProper uni m sp a
    pr m sp sh true  _ = neOfSh obj Q (JParts uni m sp false) (sh false)
    pr m sp sh false _ = neOfSh obj P (JParts uni m sp true)  (sh true)

catGuarded : (P Q : ArrNT) → G.Guarded (G.⊗e cat (catSlots P Q))
catGuarded P Q =
  G.<⊗e cat (catSlots P Q) (λ { true → ≤Slot arr P ; false → ≤Slot arr Q }) pr
  where
    pr : (m : List Val) (sp : JSplit cat m)
         (sh : (a : Bool) → G.Sh (catSlots P Q a) (JParts cat m sp a))
         (a : Bool) → G.Pos (catSlots P Q a) _ (sh a) → JProper cat m sp a
    pr m sp sh true  _ = neOfSh arr Q (JParts cat m sp false) (sh false)
    pr m sp sh false _ = neOfSh arr P (JParts cat m sp true)  (sh true)

jfGuarded : (x : NT) → G.Guarded (JF x)
jfGuarded (val , ntNum)      = G.<⌜⌝ NumG
jfGuarded (val , ntTxt)      = G.<⌜⌝ TxtG
jfGuarded (val , ntRec)      =
  G.<⊗e objOf (objOfSlots ntRecBody)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {obj}) }) (λ m sp sh a p → tt)
jfGuarded (val , ntTags)     =
  G.<⊗e arrOf (arrOfSlots ntTagsBody)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {arr}) }) (λ m sp sh a p → tt)
jfGuarded (obj , ntRecBody)  = uniGuarded ntIdMem ntTagsMem
jfGuarded (obj , ntIdMem)    =
  G.<⊗e (mem kId) (memSlots kId ntNum)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {obj}) }) (λ m sp sh a p → tt)
jfGuarded (obj , ntTagsMem)  =
  G.<⊗e (mem kTags) (memSlots kTags ntTags)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {obj}) }) (λ m sp sh a p → tt)
jfGuarded (val , ntRec3)     =
  G.<⊗e objOf (objOfSlots ntRec3Body)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {obj}) }) (λ m sp sh a p → tt)
jfGuarded (obj , ntRec3Body) = uniGuarded ntIdMem ntTagsName
jfGuarded (obj , ntTagsName) = uniGuarded ntTagsMem ntNameMem
jfGuarded (obj , ntNameMem)  =
  G.<⊗e (mem kName) (memSlots kName ntTxt)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {obj}) }) (λ m sp sh a p → tt)
jfGuarded (arr , ntTagsBody) = catGuarded ntNumElem ntTxtElem
jfGuarded (arr , ntNumElem)  =
  G.<⊗e one (oneSlots ntNum)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {arr}) }) (λ m sp sh a p → tt)
jfGuarded (arr , ntTxtElem)  =
  G.<⊗e one (oneSlots ntTxt)
        (λ { true → G.≤Var _ ; false → G.≤⌜⌝ (⊤G {arr}) }) (λ m sp sh a p → tt)

-- THE DECISION PROCEDURE. `Chart s` is ONE GRAMMAR holding the decision
-- for every nonterminal OF SORT s at the current carrier, and `SortFam` is
-- a chart at every sort at once -- which is exactly what a many-sorted
-- `löb` needs.

open DecEnum  jsonFib    using (⊗at; Refutes; dec-⊗-cuts; slotMiss)
open DecGuard jsonGraded using (SortFam; ▷ᴬ; löbᵍ; dec-⊗▷; resourceOf)

Chart : SortFam ℓ-zero
Chart s = &ᴰ (V s) (λ P → Dec⟨ DerivAt (s , P) ⟩)

chartAt : (s : JSort) (P : V s) → Chart s ⊢ Dec⟨ DerivAt (s , P) ⟩
chartAt s P = &ᴰ-E (V s) {B = λ Q → Dec⟨ DerivAt (s , Q) ⟩} P

-- the DUMMY slot of a join: `⌜ ⊤G ⌝`, decided affirmatively
decDummy : (s : JSort) → Chart s ⊢ Dec⟨ Liftg (⊤G {s}) ⟩
decDummy s = dec-yes (Liftg ⊤G) ∘g liftg ∘g ⊤-I

-- ONE SLOT of a binary rule: the nonterminal, from the chart, and its
-- resource certificate, from `probeR`.
decSlot : (s : JSort) (P : V s) → Chart s ⊢ Dec⟨ SlotG s P ⟩
decSlot s P =
  dec-&ᴰ (λ b → G.⟦ NEslot s P b ⟧c Der)
  ∘g &ᴰ-I {B = λ b → Dec⟨ G.⟦ NEslot s P b ⟧c Der ⟩}
           λ { true  → chartAt s P
             ; false → dec-map (NEres s) (Liftg (NEres s)) liftg lowerg
                       ∘g probeR s ∘g ⊤-I }

-- Every rule below is one of two shapes. A JOIN has one recursive slot and
-- one dummy, and NO resource obligation -- `JProper` at a join is `Unit`,
-- so `resource` is discharged outright.
decRule : (x : NT) → ▷ᴬ Chart {fst x} ⊢ Dec⟨ LayerAt x ⟩
decRule (val , ntNum) =
  dec-map NumG (Liftg NumG) liftg lowerg ∘g probeNum ∘g ⊤-I
decRule (val , ntTxt) =
  dec-map TxtG (Liftg TxtG) liftg lowerg ∘g probeTxt ∘g ⊤-I
decRule (val , ntRec) =
  dec-⊗▷ objOf (λ a → G.⟦ objOfSlots ntRecBody a ⟧c Der) Chart
         (jEnum objOf) (jEnumComplete objOf)
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt obj ntRecBody ; false → decDummy obj }
decRule (val , ntTags) =
  dec-⊗▷ arrOf (λ a → G.⟦ arrOfSlots ntTagsBody a ⟧c Der) Chart
         (jEnum arrOf) (jEnumComplete arrOf)
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt arr ntTagsBody ; false → decDummy arr }
decRule (obj , ntRecBody) =
  dec-⊗▷ uni (λ a → G.⟦ uniSlots ntIdMem ntTagsMem a ⟧c Der) Chart
         (jEnum uni) (jEnumComplete uni)
         (resourceOf uni (λ a → G.⟦ uniSlots ntIdMem ntTagsMem a ⟧c Der)
                     NEres probeR
                     (λ { true → neOf obj ntIdMem ; false → neOf obj ntTagsMem })
                     uniProper boolAr boolArComplete)
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → decSlot obj ntIdMem ; false → decSlot obj ntTagsMem }
decRule (obj , ntIdMem) =
  dec-⊗▷ (mem kId) (λ a → G.⟦ memSlots kId ntNum a ⟧c Der) Chart
         (jEnum (mem kId)) (jEnumComplete (mem kId))
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt val ntNum ; false → decDummy obj }
decRule (obj , ntTagsMem) =
  dec-⊗▷ (mem kTags) (λ a → G.⟦ memSlots kTags ntTags a ⟧c Der) Chart
         (jEnum (mem kTags)) (jEnumComplete (mem kTags))
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt val ntTags ; false → decDummy obj }
decRule (val , ntRec3) =
  dec-⊗▷ objOf (λ a → G.⟦ objOfSlots ntRec3Body a ⟧c Der) Chart
         (jEnum objOf) (jEnumComplete objOf)
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt obj ntRec3Body ; false → decDummy obj }
decRule (obj , ntRec3Body) =
  dec-⊗▷ uni (λ a → G.⟦ uniSlots ntIdMem ntTagsName a ⟧c Der) Chart
         (jEnum uni) (jEnumComplete uni)
         (resourceOf uni (λ a → G.⟦ uniSlots ntIdMem ntTagsName a ⟧c Der)
                     NEres probeR
                     (λ { true → neOf obj ntIdMem ; false → neOf obj ntTagsName })
                     uniProper boolAr boolArComplete)
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → decSlot obj ntIdMem ; false → decSlot obj ntTagsName }
decRule (obj , ntTagsName) =
  dec-⊗▷ uni (λ a → G.⟦ uniSlots ntTagsMem ntNameMem a ⟧c Der) Chart
         (jEnum uni) (jEnumComplete uni)
         (resourceOf uni (λ a → G.⟦ uniSlots ntTagsMem ntNameMem a ⟧c Der)
                     NEres probeR
                     (λ { true → neOf obj ntTagsMem ; false → neOf obj ntNameMem })
                     uniProper boolAr boolArComplete)
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → decSlot obj ntTagsMem ; false → decSlot obj ntNameMem }
decRule (obj , ntNameMem) =
  dec-⊗▷ (mem kName) (λ a → G.⟦ memSlots kName ntTxt a ⟧c Der) Chart
         (jEnum (mem kName)) (jEnumComplete (mem kName))
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt val ntTxt ; false → decDummy obj }
decRule (arr , ntTagsBody) =
  dec-⊗▷ cat (λ a → G.⟦ catSlots ntNumElem ntTxtElem a ⟧c Der) Chart
         (jEnum cat) (jEnumComplete cat)
         (resourceOf cat (λ a → G.⟦ catSlots ntNumElem ntTxtElem a ⟧c Der)
                     NEres probeR
                     (λ { true → neOf arr ntNumElem ; false → neOf arr ntTxtElem })
                     catProper boolAr boolArComplete)
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → decSlot arr ntNumElem ; false → decSlot arr ntTxtElem }
decRule (arr , ntNumElem) =
  dec-⊗▷ one (λ a → G.⟦ oneSlots ntNum a ⟧c Der) Chart
         (jEnum one) (jEnumComplete one)
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt val ntNum ; false → decDummy arr }
decRule (arr , ntTxtElem) =
  dec-⊗▷ one (λ a → G.⟦ oneSlots ntTxt a ⟧c Der) Chart
         (jEnum one) (jEnumComplete one)
         (λ m sp → inl (λ _ → tt))
         (λ m sp d → decΠBool (d true) (d false))
         λ { true → chartAt val ntTxt ; false → decDummy arr }

-- one nonterminal's row: transport the decision across the fixed point
decNT : (x : NT) → ▷ᴬ Chart {fst x} ⊢ Dec⟨ DerivAt x ⟩
decNT x = dec-map (LayerAt x) (DerivAt x) (rollD x) (unrollD x) ∘g decRule x

-- THE LÖB STEP, a term of the calculus, at every sort.
step : (s : JSort) → ▷ᴬ Chart {s} ⊢ Chart s
step s = &ᴰ-I {B = λ P → Dec⟨ DerivAt (s , P) ⟩} (λ P → decNT (s , P))

chart : (s : JSort) → Cover (Chart s)
chart s = löbᵍ Chart step s

derives? : (s : JSort) (P : V s) → Probe (DerivAt (s , P))
derives? s P = chartAt s P ∘g chart s

-- ... and it packages as a `Decision`, the exclusion being free
derivesDec : (s : JSort) (P : V s)
           → Decision (DerivAt (s , P)) (¬G (DerivAt (s , P)))
derivesDec s P = decDefault (DerivAt (s , P)) (derives? s P)

-- the observation: a `⊤G ⊢ Δ Bool`, read by `run` only in a test
derives! : (s : JSort) (P : V s) → ⊤G {s} ⊢ Δ Bool
derives! s P = okA (DerivAt (s , P)) (¬G DerivAt (s , P)) ∘g derives? s P
