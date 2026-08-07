{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A SMALL MODEL OF RUST, AND WHY `Box::new` IS THE RIGHT TARGET FOR A
  LINEAR SOURCE LANGUAGE.

  ------------------------------------------------------------------
  THE ARGUMENT: LINEAR ⊂ AFFINE, AND RUST IS AFFINE
  ------------------------------------------------------------------

  Rust's ownership discipline is AFFINE: a value has exactly one owner,
  moving it invalidates the source, and a value MAY be dropped (that is
  what `Drop::drop` and end-of-scope are).  It is not linear -- nothing
  forces you to use a binding.

  `TheoryGrammar.Instances.Affine.Contrast` proves both halves of the
  comparison this backend rests on:

      lin→aff    : Use⊎ u v w → Aff⊎ u v w          -- every linear
      linTm→aff  : Tm u → ATm u                     -- splitting/term is
                                                    -- affine, at the
                                                    -- SAME usage
      lin⊊aff    : Aff⊎ (false ∷ []) (false ∷ []) (true ∷ [])
                                                    -- and strictly so:
                                                    -- `adrop` is affine
                                                    -- but not linear

  So compiling the LINEAR fragment into Rust is sound for a reason, not
  by fiat: the source's ownership discipline is a SUBSET of the target's.
  Concretely, `adrop` -- the affine splitting where the whole owns a
  variable and neither premise claims it -- is the constructor that
  `Use⊎` does not have, and it is precisely the constructor that would
  force a `drop` into the emitted code.  Because the source is linear,
  NO VALUE IS EVER DROPPED in the fragment this file compiles, and so
  the emitted Rust needs no `drop`, no `Rc`, no `Clone` and no borrow.
  That is why the backend is honest rather than decorative: the reason
  the emitted code compiles under `rustc`'s borrow checker is a theorem
  about the source calculus, four modules away.

  ------------------------------------------------------------------
  THE FRAGMENT, AND WHAT IS DELIBERATELY LEFT OUT
  ------------------------------------------------------------------

  Program text in this framework is a FREE MONOID (`ISA.Program` at an
  alphabet of statements), so the model is STRAIGHT-LINE by
  construction: a sequence of statements, concatenation as the monoid
  operation.  Three statements:

      unitS        `();`                          -- skip
      letS n x     `let xn: Box<u8> = Box::new(x);`  -- DETERMINISTIC:
                                                     -- the binding names
                                                     -- its arena slot
      boxS x       `let _ = Box::new(x);`            -- NONDETERMINISTIC:
                                                     -- the allocator
                                                     -- chooses the slot

  DELIBERATELY ABSENT, and each for a stated reason:

    * `if` / `match` / `while` / `loop`.  Program text here is the free
      monoid on statements; a conditional is not a word, it is a
      coproduct, and the monoid has none.  A sibling investigation is
      looking at what promodel program text with branching should be.
      Nothing in this file works around the absence.
    * `fn` definitions and calls, `struct`s, generics, traits.  Nothing
      in the spec needs them; the emitted program is ONE function body.
    * BORROWS (`&T`, `&mut T`) and LIFETIMES.  A borrow is a
      non-owning, temporarily shared view -- the affine promodel's
      splitting has no room for it, and the linear source never asks
      for one.
    * `drop` and end-of-scope destruction.  See the argument above: the
      source is LINEAR, so `adrop` never occurs and no value is
      dropped.  This is the one omission that is a THEOREM rather than
      a scoping decision.
    * Types other than `Box<u8>`.  `Val` is three-valued (`v0 v1 v2`)
      exactly as in `Heap/Base`, so every cell is a closed reducible
      term and every test below is `refl`.

  ------------------------------------------------------------------
  THE OBSERVABLE, AND THE MEMORY MODEL
  ------------------------------------------------------------------

  The observable is `TheoryGrammar.Instances.Heap.Base.Heap` -- the
  shared specification, unchanged, the same one `Compile.LinToISA` and
  the C backend use.  `Box::new` is an OWNING HEAP ALLOCATION, so the
  identification is the obvious one: a live box is a cell.

  The model of ADDRESSES is a bump arena: the box bound at binding site
  `n` occupies address `n`.  That is what `letS` records, and it is the
  Rust reading of `LinLam/Codegen.lay`'s "variable position `i` lives at
  address `i`", including the GAPS -- a dead position allocates nothing
  and its address is simply not used.

  ------------------------------------------------------------------
  THE TRADE, INHERITED VERBATIM FROM `LinToISA/Machine`
  ------------------------------------------------------------------

      DETERMINISM buys EXECUTION.  `letS n x` is `fn (_++h single n x)`,
      so `wp` at it is reindexing (`wp-fn`, Yoneda), its Hoare axiom is
      `⌈⌉-E` at a point, and `evalStmt` can run it.

      NONDETERMINISM buys FRAMING.  `boxS x` does not name its address,
      and `ISA.Toy.localAlloc` proves that a command which does not
      choose is `Local`: fresh for the whole is fresh for both slots of
      any splitting, so the frame comes back LITERALLY unchanged.

  And this trade is not an artefact here; it is the honest reading of
  Rust.  A real `Box::new` is `boxS`: `rustc` does not tell you the
  address, the ALLOCATOR picks it, and that is exactly why one `Box`
  can never alias another.  `letS` is the arena refinement one adopts in
  order to say what the resulting heap IS, and `noLetLocal` below proves
  that naming the address costs you the frame rule -- the same theorem
  as `LinToISA/Machine.noPutLocal` and, one layer up,
  `LinLam/Codegen.noPackPres`.

  ------------------------------------------------------------------
  WHAT IS REUSED
  ------------------------------------------------------------------

  Sequencing, the empty program, consequence and framing are NOT proved
  here.  They arrive through the single line

      open import ISA.Program heapFib RStmt rstep public

  whose entire obligation -- "`sem` is a monoid homomorphism" -- was
  discharged once in `ISA.Program`.  `ISA.Toy.Alloc`, `ISA.Toy.allocAx`
  and `ISA.Toy.localAlloc` are IMPORTED, not restated: they are facts
  about `heapFib`, and nothing in them mentions an instruction alphabet.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `Place`, `rstep` (a machine must be defined
  somewhere), `evalStmt` / `evalRust` / `evalRust-sound` (the one
  recursion over a program here), and the two-line `#-same-slot`.
  `letAx`, `unitAx`, `noLetLocal` and everything downstream are
  composites.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Alloc.Machine where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

-- the TARGET promodel, qualified: `Heap/Base` has its own `boolΠ` and
-- `ISA.Machine` has another, so exactly one may be unqualified
import TheoryGrammar.Instances.Heap.Base as HB
open HB using ( Loc ; Val ; v0 ; v1 ; v2 ; Cell ; Heap ; single ; _++h_
              ; Diff ; Fresh ; _#_ ; IsNil ; Ilv ; nil ; left ; right
              ; ilv-nilL ; ilv-nilR ; heapFib ) public

-- `Alloc`, its Hoare axiom and its LOCALITY, imported.  All three are
-- statements about `heapFib` alone.
import ISA.Toy as Toy

import ISA.Machine
module M = ISA.Machine heapFib

-- ==================================================================
-- THE STATEMENT SET.  Straight-line Rust, three forms.
-- ==================================================================

data RStmt : Type₀ where
  unitS : RStmt              -- `();`
  letS  : Loc → Val → RStmt  -- `let xN: Box<u8> = Box::new(V);`
  boxS  : Val → RStmt        -- `let _ = Box::new(V);`

-- PRIMITIVE (phase 1): the arena allocation at a NAMED slot.  Being an
-- `fn` is the whole of it -- `wp` at a function is the Cartesian lift,
-- so `letAx` below is the Yoneda lemma and `evalStmt` is the function.
Place : Loc → Val → M.Cmd
Place l x = M.fn (λ h → h ++h single l x)

-- PRIMITIVE (phase 1): the machine.  The ONLY thing the generic Hoare
-- layer asks a concrete statement set for.
rstep : RStmt → M.Cmd
rstep unitS      = M.skip
rstep (letS l x) = Place l x
rstep (boxS x)   = Toy.Alloc x

-- ... and here is the whole instantiation: sequencing, the empty
-- program, consequence and the frame rule, all of them, for free.
open import ISA.Program heapFib RStmt rstep public

-- program text, under the name the spec uses
RustProg : Type₀
RustProg = Program

-- ==================================================================
-- THE HOARE AXIOMS.  None of them matches a heap.
-- ==================================================================

-- `letS` is deterministic, so its axiom is `wp-fn` (reindexing along
-- the function) transposed by `⌈⌉-E` (Yoneda).  No induction.
letAx : (l : Loc) (x : Val) (h : Heap)
      → ⟪ ⌈ h ⌉ ⟫ Place l x ⟪ ⌈ h ++h single l x ⌉ ⟫
letAx l x h =
  ⌈⌉-E {a = h} {B = wp (Place l x) ⌈ h ++h single l x ⌉}
       ( wp-fn (λ k → k ++h single l x) ⌈ h ++h single l x ⌉ h .Iso.inv
               (⌈⌉-pt (h ++h single l x)) )

-- `();` needs no axiom at all: it is `skipRule`.
unitAx : (Q : Gr) → ⟪ Q ⟫ rstep unitS ⟪ Q ⟫
unitAx = skipRule

-- the honest `Box::new`: the allocator chooses, so the postcondition is
-- an existential over the address.  `ISA.Toy`'s axiom, verbatim.
boxAx : (x : Val) (u : Heap)
      → ⟪ ⌈ u ⌉ ⟫ rstep (boxS x) ⟪ ⊕ᴰ Loc (λ l → ⌈ u ++h single l x ⌉) ⟫
boxAx = Toy.allocAx

-- ... and its locality, likewise.  THIS is the property that makes a
-- `Box` framable, and it is exactly "the allocator, not the program,
-- picks the address".
boxLocal : (x : Val) → Local (rstep (boxS x))
boxLocal = Toy.localAlloc

-- ==================================================================
-- THE NEGATIVE HALF: NAMING THE SLOT BREAKS THE FRAME RULE.
--
-- Split `l ↦ y` as `[] ⊎ (l ↦ y)` and run `letS l x` on it.  The left
-- part is `[]`, so `Local` forces the output's left slot to be `l ↦ x`,
-- while the frame slot must still be `l ↦ y` -- two boxes at one
-- address, which `Diff l l = ⊥` refutes.
--
-- Read as Rust: an arena allocation that hard-codes its own address is
-- not composable with an arbitrary surrounding region, and that is the
-- formal content of "let the allocator choose".
-- ==================================================================

-- PRIMITIVE (phase 1): the one match on `_#_`'s representation.
#-same-slot : (l : Loc) (x y : Val) → single l x # single l y → ⊥
#-same-slot l x y ((d , _) , _) = HB.diff-irrefl l d

noLetLocal : (l : Loc) (x y : Val) → Local (Place l x) → ⊥
noLetLocal l x y loc =
  #-same-slot l x y
    (HB.#-Eq (Eq.sym (r .snd .fst)) (r .snd .snd)
             (r .fst .snd .snd .snd))
  where
  h : Heap
  h = single l y

  spl : heapFib .Split appop h
  spl = [] , single l y , ilv-nilL (single l y) , tt

  r = loc h spl (h ++h single l x) Eq.refl

-- ==================================================================
-- THE EXECUTABLE FRAGMENT.
--
-- `Placed` marks the statements that are functions, `AllPlaced` the
-- programs built from them.  `boxS` is deliberately outside: it has no
-- evaluator because it has no chosen address, which is precisely the
-- property `boxLocal` turns into the frame rule.
-- ==================================================================

-- PRIMITIVE (phase 1): the machine, as a function.
evalStmt : RStmt → Heap → Heap
evalStmt unitS      h = h
evalStmt (letS l x) h = h ++h single l x
evalStmt (boxS x)   h = h        -- unreachable: `Placed (boxS x) = ⊥`

-- PRIMITIVE (phase 1): THE ONE recursion over a program in this file.
evalRust : RustProg → Heap → Heap
evalRust []      h = h
evalRust (s ∷ p) h = evalRust p (evalStmt s h)

Placed : RStmt → Type₀
Placed unitS      = Unit
Placed (letS _ _) = Unit
Placed (boxS _)   = ⊥

AllPlaced : RustProg → Type₀
AllPlaced []      = Unit
AllPlaced (s ∷ p) = Placed s × AllPlaced p

-- ==================================================================
-- ... AND THE BRIDGE.  `evalRust` is a run of `sem`, so a Hoare triple
-- about `sem p` is a statement about the machine that runs `p`.
--
-- The only place the two presentations of the language -- the
-- relational one the Hoare rules are about, and the functional one
-- that computes -- are identified.  Three clauses.
-- ==================================================================

-- PRIMITIVE (phase 1)
evalRust-sound : (p : RustProg) → AllPlaced p → (h : Heap)
               → sem p h (evalRust p h)
evalRust-sound []             _        h = Eq.refl
evalRust-sound (unitS ∷ p)    (_ , ds) h = h , Eq.refl , evalRust-sound p ds h
evalRust-sound (letS l x ∷ p) (_ , ds) h =
  h ++h single l x , Eq.refl , evalRust-sound p ds (h ++h single l x)
evalRust-sound (boxS x ∷ p)   (() , _) h

-- ==================================================================
-- THE OBSERVATION RULE, once, for every program at once.
--
-- A triple `⟪ ⌈ h ⌉ ⟫ p ⟪ ⌈ k ⌉ ⟫ᵖ` between representables says exactly
-- that running `p` from `h` lands on `k`.  This is the only exit from
-- the calculus in this backend, and everything downstream uses it in a
-- `refl` line.
-- ==================================================================

observe : (p : RustProg) → AllPlaced p → (h k : Heap)
        → ⟪ ⌈ h ⌉ ⟫ p ⟪ ⌈ k ⌉ ⟫ᵖ → evalRust p h Eq.≡ k
observe p d h k t = t h (⌈⌉-pt h) (evalRust p h) (evalRust-sound p d h)
