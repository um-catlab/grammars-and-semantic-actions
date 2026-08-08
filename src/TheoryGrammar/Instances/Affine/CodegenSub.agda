{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- AFFINE CODE GENERATION, REPAIRED: THE PASS INTO THE LEAKY HEAP. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Affine.CodegenSub where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (¬m<m; suc-≤-suc; zero-≤)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.CarrierMap

-- the SOURCE theory, opened plainly: every `⊢`-combinator below is the
-- affine-context one
open import TheoryGrammar.Instances.Affine.Syntax public

-- the EXACT target, qualified.  `Graded` rather than `Base` only for
-- `ilvLenL<`, the length lemma §1 turns on.
import TheoryGrammar.Instances.Heap.Graded as H

-- the LEAKY target, qualified: the repair, built independently
import TheoryGrammar.Instances.LeakyHeap.Base as L

-- THE ALLOCATOR, and the linear phase 4 it belongs to
import TheoryGrammar.Instances.LinLam.Codegen as CG

-- RESULT 1 AND RESULT 2 at the affine source, imported, not restated
import TheoryGrammar.Instances.Affine.Codegen as AC

-- §0  What is inherited.  Nothing here is new; the aliases exist so
-- that nothing below silently re-derives a twin.

layout : Usage → H.Heap
layout = CG.layout

-- RESULT 1 (`Affine/Codegen.apartLayA`): NO-ALIASING SURVIVES.  Used
-- verbatim as the `_#_` component of every splitting produced below --
-- the affine pass does not prove disjointness again, it consumes it.
apartAff : ∀ {u₁ u₂ u} → Aff⊎ u₁ u₂ u → (i : ℕ) → CG.lay i u₁ H.# CG.lay i u₂
apartAff = AC.apartLayA

-- §1 THE FAILURE IS NOT ABOUT THE LAYOUT: A RIGIDITY THEOREM.

eqTrans : {A : Type₀} {x y z : A} → x Eq.≡ y → y Eq.≡ z → x Eq.≡ z
eqTrans Eq.refl q = q

-- transport of `Ilv` along `Eq`, so nothing below needs a Path
ilv-Eq : {a a' b b' c : H.Heap}
       → a Eq.≡ a' → b Eq.≡ b' → H.Ilv a b c → H.Ilv a' b' c
ilv-Eq Eq.refl Eq.refl p = p

-- an exhausted usage splits as itself, twice -- by `askip` alone.
-- (`Base.affDiag` is the converse: ONLY an exhausted usage does.)
affDiagEmpty : (u : Usage) → Empty u → Aff⊎ u u u
affDiagEmpty []          e = anil
affDiagEmpty (true  ∷ u) e = E.rec e
affDiagEmpty (false ∷ u) e = askip (affDiagEmpty u e)

-- `Ilv` adds lengths, so nothing interleaves with itself to give itself
-- except the empty heap.  `H.ilvLenL<` is the graded lemma.
ilvSelf : (k : H.Heap) → H.Ilv k k k → H.IsNil k
ilvSelf []      p = tt
ilvSelf (c ∷ k) p = ¬m<m (H.ilvLenL< p (suc-≤-suc zero-≤))

nilEq : (h : H.Heap) → H.IsNil h → h Eq.≡ []
nilEq []      n = Eq.refl
nilEq (c ∷ h) n = E.rec n

notNil : {l : H.Loc} {x : H.Val} {h : H.Heap} → ((l , x) ∷ h) Eq.≡ [] → ⊥
notNil ()

-- the same reindexing, read into the `_#_`-free fragment
cellOf : Reindex affFib H.heapFib → Reindex affFib H.cellFib
cellOf h .hom = h .hom

forgetPres : (h : Reindex affFib H.heapFib)
           → SplitPresAt h appop → SplitPresAt (cellOf h) appop
forgetPres h P .homSplit u sp =
    P .homSplit u sp .fst
  , P .homSplit u sp .snd .fst
  , P .homSplit u sp .snd .snd .fst
forgetPres h P .homParts u sp = P .homParts u sp

-- STEP (1): at an EMPTY usage the diagonal exists, so `hom` is `[]`.
zerosTrivial : (h : Reindex affFib H.cellFib) → SplitPresAt h appop
             → (u : Usage) → h .hom tt (zeros u) Eq.≡ []
zerosTrivial h P u = nilEq _ (ilvSelf _ (ilv-Eq e₁ e₂ ilv))
  where
  z : Usage
  z = zeros u

  sp : affFib .Split appop z
  sp = z , z , affDiagEmpty z (zerosEmpty u)

  ilv : H.Ilv (P .homSplit z sp .fst) (P .homSplit z sp .snd .fst)
              (h .hom tt z)
  ilv = P .homSplit z sp .snd .snd

  e₁ : P .homSplit z sp .fst Eq.≡ h .hom tt z
  e₁ = P .homParts z sp true

  e₂ : P .homSplit z sp .snd .fst Eq.≡ h .hom tt z
  e₂ = P .homParts z sp false

-- STEP (2): `affDropAll` -- everything may be dropped -- then forces the
-- WHOLE to be `[]` as well.
affCellTrivial : (h : Reindex affFib H.cellFib) → SplitPresAt h appop
               → (u : Usage) → h .hom tt u Eq.≡ []
affCellTrivial h P u = Eq.sym (H.ilv-nilL-inv (ilv-Eq e₁ e₂ ilv))
  where
  sp : affFib .Split appop u
  sp = zeros u , zeros u , affDropAll u

  ilv : H.Ilv (P .homSplit u sp .fst) (P .homSplit u sp .snd .fst)
              (h .hom tt u)
  ilv = P .homSplit u sp .snd .snd

  e₁ : P .homSplit u sp .fst Eq.≡ []
  e₁ = eqTrans (P .homParts u sp true) (zerosTrivial h P u)

  e₂ : P .homSplit u sp .snd .fst Eq.≡ []
  e₂ = eqTrans (P .homParts u sp false) (zerosTrivial h P u)

affHeapTrivial : (h : Reindex affFib H.heapFib) → SplitPresAt h appop
               → (u : Usage) → h .hom tt u Eq.≡ []
affHeapTrivial h P = affCellTrivial (cellOf h) (forgetPres h P)

-- `Affine/Codegen.noAffPres` again, now as a COROLLARY of rigidity
-- rather than of one bad cell: `layout (true ∷ [])` is not empty.
noAffPres' : SplitPresAt AC.affLayoutMap appop → ⊥
noAffPres' P = notNil (affHeapTrivial AC.affLayoutMap P (true ∷ []))

-- §2 THE TWO FRAGMENTS OF `heapFib` ARE DIFFERENT `Fibered`.

fragmentsDiffer : LaxPoint H.cellFib × (LaxPoint L.leakyFib → ⊥)
fragmentsDiffer = H.cellPoint , L.noLeakyPoint

-- ... and at the level of splittings, in both directions. a `leakyFib`
-- splitting with no `cellFib` counterpart at the same parts: THE DROP
-- (`L.subIlv⊋ilv`, and `AC.noIlvGap` is result 2's obstruction at the same
-- cell).
leakyNotCell : L.SubIlv [] [] (H.single 0 H.v1)
             × (H.Ilv [] [] (H.single 0 H.v1) → ⊥)
leakyNotCell = L.leak L.snil , AC.noIlvGap

-- a `cellFib` splitting with no `leakyFib` counterpart at the same
-- parts: THE ALIAS.  `LeakySplit` kept `_#_`, and `#-self` refutes it.
cellNotLeaky : H.CellSplit appop ((0 , H.v1) ∷ (0 , H.v1) ∷ [])
             × (H.single 0 H.v1 H.# H.single 0 H.v1 → ⊥)
cellNotLeaky =
    (H.single 0 H.v1 , H.single 0 H.v1 , H.left (H.right H.nil))
  , H.#-self 0 H.v1

-- §4 A LEAKY SPLITTING IS AN EXACT ONE PLUS A HEAP OF DROPPED CELLS.

subIlv→drops : ∀ {h₁ h₂ h} → L.SubIlv h₁ h₂ h
             → Σ[ m ∈ H.Heap ] Σ[ d ∈ H.Heap ]
                 (H.Ilv h₁ h₂ m × H.Ilv m d h)
subIlv→drops L.snil = [] , [] , H.nil , H.nil
subIlv→drops (L.sleft p) =
  let (m , d , i₁ , i₂) = subIlv→drops p in _ ∷ m , d , H.left i₁ , H.left i₂
subIlv→drops (L.sright p) =
  let (m , d , i₁ , i₂) = subIlv→drops p in _ ∷ m , d , H.right i₁ , H.left i₂
subIlv→drops (L.leak p) =
  let (m , d , i₁ , i₂) = subIlv→drops p in m , _ ∷ d , i₁ , H.right i₂

drops→subIlv : ∀ {h₁ h₂ m d h}
             → H.Ilv h₁ h₂ m → H.Ilv m d h → L.SubIlv h₁ h₂ h
drops→subIlv H.nil        H.nil        = L.snil
drops→subIlv (H.left  i₁) (H.left i₂)  = L.sleft  (drops→subIlv i₁ i₂)
drops→subIlv (H.right i₁) (H.left i₂)  = L.sright (drops→subIlv i₁ i₂)
drops→subIlv i₁           (H.right i₂) = L.leak   (drops→subIlv i₁ i₂)

-- §3 SPLIT PRESERVATION AT THE REPAIRED TARGET. **HOLDS.**
-- `LinLam/Codegen.ilvLay` was a constructor-for-constructor translation
-- with no arithmetic; so is this, with `adrop ↦ leak` the new line.

leakLay : ∀ {u₁ u₂ u} → Aff⊎ u₁ u₂ u → (i : ℕ)
        → L.SubIlv (CG.lay i u₁) (CG.lay i u₂) (CG.lay i u)
leakLay anil       i = L.snil
leakLay (aleft  s) i = L.sleft  (leakLay s (suc i))
leakLay (aright s) i = L.sright (leakLay s (suc i))
leakLay (askip  s) i = leakLay s (suc i)
leakLay (adrop  s) i = L.leak   (leakLay s (suc i))    -- <-- `adrop ↦ leak`

affLeakMap : Reindex affFib L.leakyFib
affLeakMap .hom _ = layout

affLeakPres : (o : MonOp) → SplitPresAt affLeakMap o

affLeakPres nilop .homSplit u e  = AC.emptyLayA u 0 e
affLeakPres nilop .homParts u e ()

affLeakPres appop .homSplit u (u₁ , u₂ , s) =
  layout u₁ , layout u₂ , leakLay s 0 , apartAff s 0
affLeakPres appop .homParts u (u₁ , u₂ , s) =
  boolΠ {M = λ a → boolΠ {M = λ _ → H.Heap} (layout u₁) (layout u₂) a
                     Eq.≡ layout (boolΠ {M = λ _ → Usage} u₁ u₂ a)}
        Eq.refl Eq.refl

module A = Along affLeakMap

-- ... AND REFLECTION, the stronger half, which also survives.

reflNilAff : (u : Usage) (i : ℕ) → H.IsNil (CG.lay i u) → Empty u
reflNilAff []          i n = tt
reflNilAff (true  ∷ u) i n = n           -- both sides are `⊥`
reflNilAff (false ∷ u) i n = reflNilAff u (suc i) n

reflSub : (u : Usage) (i : ℕ) {h₁ h₂ : H.Heap}
        → L.SubIlv h₁ h₂ (CG.lay i u) → h₁ H.# h₂
        → Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ]
            (Aff⊎ u₁ u₂ u × ((h₁ Eq.≡ CG.lay i u₁) × (h₂ Eq.≡ CG.lay i u₂)))
reflSub []          i L.snil       d = [] , [] , anil , Eq.refl , Eq.refl
reflSub (true  ∷ u) i (L.sleft  p) d =
  let (a , b , s , e₁ , e₂) = reflSub u (suc i) p (d .snd)
  in true ∷ a , false ∷ b , aleft s , Eq.ap ((i , H.v1) ∷_) e₁ , e₂
reflSub (true  ∷ u) i (L.sright p) d =
  let (a , b , s , e₁ , e₂) = reflSub u (suc i) p (CG.#-tail-r _ _ i H.v1 d)
  in false ∷ a , true ∷ b , aright s , e₁ , Eq.ap ((i , H.v1) ∷_) e₂
reflSub (true  ∷ u) i (L.leak   p) d =
  let (a , b , s , e₁ , e₂) = reflSub u (suc i) p d
  in false ∷ a , false ∷ b , adrop s , e₁ , e₂         -- <-- `leak ↦ adrop`
reflSub (false ∷ u) i p            d =
  let (a , b , s , e₁ , e₂) = reflSub u (suc i) p d
  in false ∷ a , false ∷ b , askip s , e₁ , e₂

affLeakRefl : (o : MonOp) → A.ReflectsSplitAt o
affLeakRefl nilop u n = reflNilAff u 0 n , λ ()
affLeakRefl appop u (h₁ , h₂ , p , d) =
  let (u₁ , u₂ , s , e₁ , e₂) = reflSub u 0 p d
  in (u₁ , u₂ , s)
   , boolΠ {M = λ a → boolΠ {M = λ _ → H.Heap} h₁ h₂ a
                        Eq.≡ layout (boolΠ {M = λ _ → Usage} u₁ u₂ a)}
           e₁ e₂

-- §5  PHASE 2 FROM HERE DOWN.  `Lay` reinterprets an intuitionistic
-- separation predicate as a predicate on affine contexts; the two
-- directions of strong monoidality are `push⊗` and `pull⊗`.

Lay : L.Gr → Ctx
Lay B = A.pull {s = tt} B

respellIn : (B C : L.Gr) (a : Bool)
          → boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a
          ⊢ Lay (boolΠ {M = λ _ → L.Gr} B C a)
respellIn B C =
  boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a
                 ⊢ Lay (boolΠ {M = λ _ → L.Gr} B C a)}
        idg idg

respellOut : (B C : L.Gr) (a : Bool)
           → Lay (boolΠ {M = λ _ → L.Gr} B C a)
           ⊢ boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a
respellOut B C =
  boolΠ {M = λ a → Lay (boolΠ {M = λ _ → L.Gr} B C a)
                 ⊢ boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a}
        idg idg

-- AFFINE CONTEXT SPLITTING BECOMES INTUITIONISTIC HEAP SEPARATION.
-- Its proof is `affLeakPres appop`: no-aliasing is not established
-- here, it is what `push⊗` consumed.
layLeak∗ : (B C : L.Gr) → (Lay B ⊛ Lay C) ⊢ Lay (B L.∗ C)
layLeak∗ B C =
    A.push⊗ appop (affLeakPres appop) {B = boolΠ {M = λ _ → L.Gr} B C}
  ∘g ⊗ˢ-map appop
       {A = boolΠ {M = λ _ → Ctx} (Lay B) (Lay C)}
       {B = λ a → Lay (boolΠ {M = λ _ → L.Gr} B C a)}
       (respellIn B C)

-- ... and back, by reflection.  Together: `Lay` is STRONG monoidal.
layLeak∗⁻ : (B C : L.Gr) → Lay (B L.∗ C) ⊢ (Lay B ⊛ Lay C)
layLeak∗⁻ B C =
    ⊗ˢ-map appop
      {A = λ a → Lay (boolΠ {M = λ _ → L.Gr} B C a)}
      {B = boolΠ {M = λ _ → Ctx} (Lay B) (Lay C)}
      (respellOut B C)
  ∘g A.pull⊗ appop (affLeakRefl appop) {B = boolΠ {M = λ _ → L.Gr} B C}

-- the unit, both ways: "nothing is owned" ⊣⊢ "the empty heap"
layEmp : 𝟙 ⊢ Lay L.emp
layEmp = A.push⊗ nilop (affLeakPres nilop) {B = λ ()}

layEmp⁻ : Lay L.emp ⊢ 𝟙
layEmp⁻ = A.pull⊗ nilop (affLeakRefl nilop) {B = λ ()}

-- §6 TRANSPORT. RESULT 1, EXPORTED INTERNALLY.

noDupAffLay : (l : H.Loc) (x : H.Val)
            → (Lay L.⌈ H.single l x ⌉ ⊛ Lay L.⌈ H.single l x ⌉) ⊢ ⊥G
noDupAffLay l x =
    A.pullTerm (L.apart-self l x)
  ∘g layLeak∗ L.⌈ H.single l x ⌉ L.⌈ H.single l x ⌉

-- the frame rule, pulled back the same way
layFrame : {B B' : L.Gr} (C : L.Gr) → B L.⊢ B'
         → (Lay B ⊛ Lay C) ⊢ (Lay B' ⊛ Lay C)
layFrame {B} {B'} C f =
  layLeak∗⁻ B' C ∘g A.pullTerm (L.frame C f) ∘g layLeak∗ B C

-- §7  EMITTING CODE, and observation.  `run` only in a `refl` line.

Code : Ctx
Code = ⊕ᴰ H.Heap (λ h → Lay L.⌈ h ⌉)

-- PRIMITIVE (phase 1): `⊕ᴰ-I` at the index itself -- the ONE place the
-- pass names its own output.
emit : {B : Ctx} → B ⊢ Code
emit u _ = ⊕ᴰ-I H.Heap {A = λ h → Lay L.⌈ h ⌉} (layout u) u
             (L.⌈⌉-pt (layout u))

emitTm : ATmG ⊢ Code
emitTm = emit

-- Terms.  `dropAff` and `dropApp` are the shapes `LinLam.Tm` cannot
-- express at all, and they are exactly the ones §1 refutes and §3
-- recovers.

xAff : ATm (true ∷ [])
xAff = tvar tt

dropAff : ATm (true ∷ [])                 -- owns a variable it ignores
dropAff = tdrop {false ∷ []} {true ∷ []} tt idAff0

twoSplitAff : Aff⊎ (true ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ true ∷ [])
twoSplitAff = aleft (aright anil)

twoVar : ATm (true ∷ true ∷ [])
twoVar = tapp twoSplitAff (tvar tt) (tvar tt)

idAff00 : ATm (false ∷ false ∷ [])
idAff00 = tlam (tvar tt)

dropApp : ATm (true ∷ true ∷ [])          -- the second premise DROPS
dropApp = tapp (aleft (adrop anil)) (tvar tt) idAff00

_ : emitTm [] idAff .fst ≡ []
_ = refl

_ : emitTm (true ∷ []) xAff .fst ≡ H.single 0 H.v1
_ = refl

-- the dropped variable is still ALLOCATED: the layout is about the
-- context, not about what the term reads
_ : emitTm (true ∷ []) dropAff .fst ≡ H.single 0 H.v1
_ = refl

_ : emitTm (true ∷ true ∷ []) twoVar .fst ≡ (0 , H.v1) ∷ (1 , H.v1) ∷ []
_ = refl

_ : emitTm (true ∷ true ∷ []) dropApp .fst ≡ (0 , H.v1) ∷ (1 , H.v1) ∷ []
_ = refl

-- §8  THE POINT, as `refl`s.

-- (a) the linear-shaped application still gives two DISJOINT regions;
-- the `_#_` proof reduces to a nest of `tt`, exactly as in
-- `LinLam/Codegen`.  No-aliasing survived the change of target.
_ : affLeakPres appop .homSplit (true ∷ true ∷ [])
      (true ∷ false ∷ [] , false ∷ true ∷ [] , twoSplitAff)
  ≡ ( H.single 0 H.v1
    , H.single 1 H.v1
    , L.sleft (L.sright L.snil)
    , ((tt , tt) , tt) )
_ = refl

-- (b) THE DROP.  Both parts are empty, the whole is not, and `leak` is
-- the component that accounts for the orphaned cell.  Against `heapFib`
-- this field is exactly the one `AC.noAffPres` shows cannot exist.
_ : affLeakPres appop .homSplit (true ∷ [])
      (false ∷ [] , false ∷ [] , adrop anil)
  ≡ ([] , [] , L.leak L.snil , tt)
_ = refl

-- ... and reflection inverts both
_ : affLeakRefl appop (true ∷ []) ([] , [] , L.leak L.snil , tt) .fst
  ≡ (false ∷ [] , false ∷ [] , adrop anil)
_ = refl

_ : affLeakRefl appop (true ∷ true ∷ [])
      ( H.single 0 H.v1 , H.single 1 H.v1
      , L.sleft (L.sright L.snil) , ((tt , tt) , tt) ) .fst
  ≡ (true ∷ false ∷ [] , false ∷ true ∷ [] , twoSplitAff)
_ = refl

-- the dropped cell read off as an emitted `free`: `subIlv→drops` of the
-- drop splitting is the empty exact interleaving together with the one
-- cell that must be released
_ : subIlv→drops (L.leak {c = 0 , H.v1} L.snil) .snd .fst ≡ H.single 0 H.v1
_ = refl
