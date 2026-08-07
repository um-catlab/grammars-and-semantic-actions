{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A TWO-LEVEL TOWER, END TO END.

  The smallest pair of machines for which the three `SplitPresAt`
  obligations of `TheoryGrammar.Machine.Refine` are all nontrivial and
  all provable:

      SOURCE   one instruction `inc2`, "add two"
      TARGET   one instruction `inc`,  "add one"
      compile  inc2  ↦  inc ∷ inc ∷ []
      decode   the identity on states

  Resources are ℕ split additively (`natFib`), program text is the free
  monoid on the instruction set (`freeFib`), and both machines are
  deterministic, so `Run p x y` is `run p x Eq.≡ y`.

  WHAT IS EXHIBITED, in order:

    1. `compilePres seqop`  -- compilation is a monoid homomorphism.
    2. `compilePres sepop`  -- decoding preserves separation.
    3. `compilePres runop`  -- forward simulation, via `Refine.ofSim`.
    4. `srcTriple`          -- a Hoare triple written as an internal
                               `⊢`-term of the SOURCE ISA theory.
    5. `tgtTriple`          -- the SAME term, transported by
                               `Refine.wpre-push`, now a Hoare triple
                               about the EMITTED CODE.

  Step 5 is the claim under test.  Note what it is not: `tgtTriple` is
  not reproved, and it is not obtained by running the target machine.  It
  is `srcTriple` composed with one combinator, and its type is a
  statement about `compile p₀`.

  Everything is one lemma deep: `simEq` (`trun (compile p) x ≡ srun p x`)
  supplies BOTH the forward and the backward simulation, because these
  machines are deterministic.  That coincidence is the honest reason this
  example is cheap, and it is flagged again at the bottom.
-}
module TheoryGrammar.Machine.Example where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Machine.Signature
import TheoryGrammar.Machine.Refine

-- ==================================================================
-- `Eq` housekeeping.  PRIMITIVE (phase 1), three lines.
-- ==================================================================

etrans : {A : Type₀} {x y z : A} → x Eq.≡ y → y Eq.≡ z → x Eq.≡ z
etrans Eq.refl q = q

eap : {A B : Type₀} (f : A → B) {x y : A} → x Eq.≡ y → f x Eq.≡ f y
eap f Eq.refl = Eq.refl

-- ==================================================================
-- THE TWO PROMODELS THAT ARE NOT ABOUT MACHINES.
-- ==================================================================

-- resources: ℕ, split additively
natFib : Fibered monoidSig ℓ-zero ℓ-zero
natFib .carrier _ = ℕ
natFib .Split nilop n = n Eq.≡ 0
natFib .Split appop n = Σ[ a ∈ ℕ ] Σ[ b ∈ ℕ ] (a + b Eq.≡ n)
natFib .parts nilop n sp ()
natFib .parts appop n (a , b , _) = boolΠ {M = λ _ → ℕ} a b

-- program text: the free monoid, with concatenation as its splitting
data Split3 {A : Type₀} : List A → List A → List A → Type₀ where
  snil  : ∀ {v} → Split3 [] v v
  scons : ∀ {c u v w} → Split3 u v w → Split3 (c ∷ u) v (c ∷ w)

IsNil : {A : Type₀} → List A → Type₀
IsNil []      = Unit
IsNil (_ ∷ _) = ⊥

freeFib : (A : Type₀) → Fibered monoidSig ℓ-zero ℓ-zero
freeFib A .carrier _ = List A
freeFib A .Split nilop w = IsNil w
freeFib A .Split appop w = Σ[ u ∈ List A ] Σ[ v ∈ List A ] Split3 u v w
freeFib A .parts nilop w sp ()
freeFib A .parts appop w (u , v , _) = boolΠ {M = λ _ → List A} u v

-- ==================================================================
-- THE TWO INSTRUCTION SETS AND THEIR SEMANTICS.
-- ==================================================================

data SInstr : Type₀ where inc2 : SInstr
data TInstr : Type₀ where inc  : TInstr

srun : List SInstr → ℕ → ℕ
srun []          x = x
srun (inc2 ∷ p)  x = srun p (suc (suc x))

trun : List TInstr → ℕ → ℕ
trun []         x = x
trun (inc ∷ p)  x = trun p (suc x)

SRun : List SInstr → ℕ → ℕ → Type₀
SRun p x y = srun p x Eq.≡ y

TRun : List TInstr → ℕ → ℕ → Type₀
TRun p x y = trun p x Eq.≡ y

compile : List SInstr → List TInstr
compile []         = []
compile (inc2 ∷ p) = inc ∷ inc ∷ compile p

-- THE ONE LEMMA.  Everything below is a consequence.
simEq : (p : List SInstr) (x : ℕ) → trun (compile p) x Eq.≡ srun p x
simEq []         x = Eq.refl
simEq (inc2 ∷ p) x = simEq p (suc (suc x))

-- ==================================================================
-- THE TOWER.
-- ==================================================================

module RF = TheoryGrammar.Machine.Refine
              natFib (freeFib SInstr) SRun
              natFib (freeFib TInstr) TRun

module S = RF.S
module T = RF.T

cm : Reindex S.isaFib T.isaFib
cm .hom prog = compile
cm .hom res  = λ n → n

-- ==================================================================
-- OBLIGATION 1 (seqop).  COMPILATION IS A MONOID HOMOMORPHISM.
--
-- The whole content is `csplit`: a splitting of the source program is
-- carried to a splitting of the emitted code, constructor for
-- constructor.  `scons` becomes two `scons`, because `inc2` emits two
-- instructions -- so the offsets stay in lockstep and no arithmetic
-- appears, which is the same phenomenon `LinLam/Codegen`'s `ilvLay`
-- records.
-- ==================================================================

csplit : {u v w : List SInstr} → Split3 u v w
       → Split3 (compile u) (compile v) (compile w)
csplit snil     = snil
csplit (scons {c = inc2} s) = scons (scons (csplit s))

-- ==================================================================
-- OBLIGATION 2 (sepop).  DECODING PRESERVES SEPARATION.
--
-- `decode` is the identity here, so a separating splitting maps to
-- itself.  In a real code generator this is `layPres` and is where
-- no-aliasing lives; the point of including it is that it is the SAME
-- record field, at a different operation.
-- ==================================================================

compilePres : (o : ISAOp) → SplitPresAt cm o

compilePres seqop .homSplit w (u , v , s) = compile u , compile v , csplit s
compilePres seqop .homParts w (u , v , s) =
  boolΠ {M = λ a → T.isaFib .parts seqop (compile w)
                     (compile u , compile v , csplit s) a
                   Eq.≡ cm .hom (ISASortOf seqop a)
                          (S.isaFib .parts seqop w (u , v , s) a)}
        Eq.refl Eq.refl

compilePres sepop .homSplit n sp = sp
compilePres sepop .homParts n sp =
  boolΠ {M = λ a → T.isaFib .parts sepop n sp a
                   Eq.≡ cm .hom (ISASortOf sepop a)
                          (S.isaFib .parts sepop n sp a)}
        Eq.refl Eq.refl

-- OBLIGATION 3 (runop).  FORWARD SIMULATION, through `Refine.ofSim`:
-- the record is not written out, it is built from the diagram.
compilePres runop = RF.ofSim cm sim
  where
  sim : RF.Sim cm
  sim p x y r = etrans (simEq p x) r

-- ==================================================================
-- BACKWARD SIMULATION.  Determinism makes it the same lemma read the
-- other way; see the closing note.
-- ==================================================================

bsim : RF.BackSim cm
bsim p x ŷ r̂ = srun p x , Eq.refl , etrans (Eq.sym (simEq p x)) r̂

-- ==================================================================
-- §  A PROGRAM, AND A TRIPLE ABOUT IT.
-- ==================================================================

p₀ : List SInstr
p₀ = inc2 ∷ inc2 ∷ []

-- the emitted code -- four instructions, and it computes
_ : compile p₀ ≡ inc ∷ inc ∷ inc ∷ inc ∷ []
_ = refl

_ : trun (compile p₀) 0 ≡ 4
_ = refl

-- The TARGET-level specification of the code: "the program is exactly
-- `compile p₀`".  A representable at the `prog` sort IS an individual
-- program, so no new machinery is needed to name one.
Spec₀ : T.Spec ℓ-zero
Spec₀ = T.⌈_⌉ {s = prog} (compile p₀)

Pre : T.Asrt ℓ-zero
Pre = T.⌈_⌉ {s = res} 0

Post : T.Asrt ℓ-zero
Post = T.⌈_⌉ {s = res} 4

-- the spec is in the image of the compiler, which is what lets a
-- source-level proof say anything about it
inImage : RF.InImage cm Spec₀
inImage p̂ e = p₀ , Eq.sym e , Eq.refl

-- ==================================================================
-- THE SOURCE TRIPLE, as an internal `⊢`-term of the SOURCE ISA theory.
--
-- Its precondition and postcondition are the PULLBACKS of the target
-- ones -- which here are the target ones on the nose, because `decode`
-- is the identity.  Its specification is `pull Spec₀`, i.e. "any source
-- program whose compilation is `compile p₀`" -- deliberately weaker than
-- `⌈ p₀ ⌉`, and that weakening is where `simEq` is used a second time.
-- ==================================================================

module A = Along cm

srcTriple : S.⟪_⟫_⟪_⟫ (A.pull {s = res} Pre) (A.pull {s = prog} Spec₀)
                       (A.pull {s = res} Post)
srcTriple x e (p , y , r) k = go x e p y r (k tt)
  where
  go : (x : ℕ) → x Eq.≡ 0 → (p : List SInstr) (y : ℕ)
     → srun p x Eq.≡ y → compile p Eq.≡ compile p₀ → y Eq.≡ 4
  go .0 Eq.refl p y r ce =
    etrans (Eq.sym r) (etrans (Eq.sym (simEq p 0)) (eap (λ c → trun c 0) ce))

-- ==================================================================
-- ... AND THE SAME TERM, ABOUT THE EMITTED CODE.
--
-- One combinator.  `wpre-push` is `Refine`'s backward-simulation
-- transport; nothing here inspects `compile p₀`, and no target-level
-- reasoning is performed.
-- ==================================================================

tgtTriple : T.⟪_⟫_⟪_⟫ Pre Spec₀ Post
tgtTriple = RF.wpre-push cm bsim Spec₀ inImage Post S.∘g srcTriple

-- and it is a genuine statement about the four emitted instructions:
-- fed the actual run, it returns the actual answer.
_ : tgtTriple 0 Eq.refl (compile p₀ , 4 , Eq.refl) (λ _ → Eq.refl) ≡ Eq.refl
_ = refl

-- ==================================================================
-- §  WHAT THIS EXAMPLE DOES AND DOES NOT SHOW.
--
-- SHOWS.  The three obligations of a compiler are three instances of one
-- record field (`SplitPresAt`) at the three operations of one signature,
-- and a Hoare triple moves between the levels by ONE combinator.  Steps
-- 1-3 never mention assertions; steps 4-5 never mention instructions.
--
-- DOES NOT SHOW.  Both machines are DETERMINISTIC and `decode` is the
-- IDENTITY.  Determinism is why `simEq` serves as both `Sim` and
-- `BackSim`; a nondeterministic target (a real allocator, a scheduler)
-- would make `BackSim` a genuinely separate and harder obligation, and
-- that is the standard situation.  A nontrivial `decode` is what makes
-- `compilePres sepop` say something -- here it says nothing, and
-- `LinLam/Codegen.layPres` (plus its refutation `noPackPres`) is the
-- place where that obligation is real.
-- ==================================================================
