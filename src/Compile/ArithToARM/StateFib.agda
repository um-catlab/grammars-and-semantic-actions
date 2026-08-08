{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE AArch64 MACHINE STATE AS A SEPARATING RESOURCE PROMODEL.

  ------------------------------------------------------------------
  WHAT WAS OWED
  ------------------------------------------------------------------

  `Compile.ArithToARM.AArch64`'s header says it plainly:

      "The frame rule needs a SEPARATING resource promodel, which a pair
       of total functions is not.  `stFib` below is therefore the trivial
       promodel: enough for sequencing, not enough for framing."

  and `AArch64Codegen` pays for that with `pLow` -- "memory strictly
  below the operand stack is untouched" -- proved by hand, one
  `setM-miss` per instruction, at every node of the compiler.

  This file builds the promodel that was missing.  A resource is a
  PARTIAL map

      PSt = Cell -> Maybe Word,      Cell = reg Reg | mem Word

  covering registers AND memory in one carrier, and

      Split appop s = S s1, S s2, (c : Cell) -> Join (s1 c) (s2 c) (s c)

  with `Join` the pointwise disjoint-union RELATION -- never both `just`.
  Two design points, both forced:

    * `Join` is a RELATION, so no union operation and hence NO FUNEXT is
      needed to say what a splitting is.  `Split` is a P of a small
      Unit/(=)/⊥-valued relation, exactly as `Heap.Base`'s `Ilv` is a
      small inductive family.

    * the FRAME SLOT of the transferred splitting is LITERALLY the same
      function (`tSplit` below keeps `s2`), so `Local`'s third component
      -- an equation between resources, i.e. between FUNCTIONS -- is
      `Eq.refl` and funext never appears.  This is the whole reason the
      function carrier is affordable here where `Heap.Base` had to use
      an association list: the AArch64 memory is `Word -> Word`, an
      infinite domain, so a list carrier could not even STATE agreement
      with `exec1` on total states.

  ------------------------------------------------------------------
  THE OBSTRUCTION, WITH ITS COUNTEREXAMPLE
  ------------------------------------------------------------------

  `ISA.Machine.Local` has no safety side condition -- its own header says
  so, and `ISA.Toy` records that the small-footprint store fails it.  The
  same failure is fatal HERE, for every writing instruction, and
  `no-Local-movI` below is the one-line proof:

      take s = { reg w9 |-> 0 } split as s1 = {} and s2 = s.  `movI w9 5`
      runs on s, but `Local` demands it also run on the EMPTY left part,
      and running it there means owning `reg w9` there.

  That is not a defect of this promodel; it is `Local` quantifying over
  splittings that put the written cell in the frame.  The repair is the
  standard one, and `ISA.Toy`'s header already names it and its cost:
  demand the frame property only where the command is SAFE on the left
  part, and then a composite's safety must be "safe now, and safe after
  every step".

  The pleasant surprise is that the second half needs no new notion.
  "safe after every step" IS `wp`, so

      LocalOn S c   /\   LocalOn T d   ==>   LocalOn (S & wp c T) (c ; d)

  (`localOn-comp`) and the safety of a PROGRAM is the same recursion the
  free-monoid extension already is (`SafeP`).  Everything else --
  `frameOn-wp`, `frameRuleOn`, `localOn-sem` -- is `ISA.Machine`'s
  `frame-wp` / `local-comp` / `ISA.Program.local-sem` with one extra
  argument threaded, which is the honest measure of what safety costs.

  ------------------------------------------------------------------
  READS ARE NOT PART OF THE FOOTPRINT
  ------------------------------------------------------------------

  `stepC` reads with `Rd?` -- "if the cell is owned, it holds this value;
  otherwise ANYTHING" -- so a read of an unowned cell makes the command
  NONDETERMINISTIC rather than stuck.  That is exactly the shape that
  makes `ISA.Toy`'s `alloc` local, and it buys two things: an
  instruction's safety mentions only the cells it WRITES, and the
  environment (which the compiler only ever reads) may sit in the FRAME.
  On total states nothing is lost -- `stepC-tot` -- because every cell is
  owned there; the command is a sound over-approximation of `exec1`
  everywhere else.

  ------------------------------------------------------------------
  THE PAYOFF
  ------------------------------------------------------------------

  `frameLow` is `pLow` with no arithmetic in it: locality of the program
  hands back the frame slot UNCHANGED, so "memory below the operand stack
  is untouched" is read off a splitting rather than proved by a
  `setM-miss` at every node.  `push9Low` instantiates it at
  `AArch64Codegen`'s own push macro and is a composite -- no `lt-neq`, no
  `setM-miss`, no induction.

  What is still owed for the whole of `compile e` is exactly one thing,
  and it is now the RIGHT thing: `SafeP (compile e) s1`, the statement
  that the compiled code only ever writes cells it owns.  That is an
  ownership invariant (Unit/⊥-valued), not a statement about memory
  CONTENTS, and it is the honest replacement for `pLow`'s hand proof.
  `compileSafe` proves it (one induction over `e`, no arithmetic beyond
  `Ge`), and `compileLow` is then `pLow` itself -- `pLow-same` below
  typechecks only because the two statements are definitionally the same
  type.

  The promodel is genuinely a promodel: `noPoint` refutes `LaxPoint
  stFib`, since a partial map has no total join.  The multiplicatives and
  additives are unaffected -- `FibNotation`/`RulesF` never ask for a
  point -- and nothing here wants `Bridge` or `Honest`.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout: this file BUILDS a promodel and its primitives.
  Everything from `LocalOn` onwards is generic in the promodel except
  where it names `Cell`.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.StateFib where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Maybe using (Maybe; nothing; just)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.List using (List; []; _∷_; _++_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

open import Compile.ArithToARM.AArch64

-- ==================================================================
-- §1  CELLS, AND APARTNESS OF CELLS.
--
-- One carrier for registers AND memory.  `Dif` is `Heap.Base`'s
-- apartness verbatim -- Unit/⊥-valued, so a proof is `tt` and never
-- blocks a reduction.
-- ==================================================================

data Cell : Type₀ where
  reg : Reg → Cell
  mem : Word → Cell

Dif : ℕ → ℕ → Type₀                               -- PRIMITIVE
Dif zero    zero    = ⊥
Dif zero    (suc _) = Unit
Dif (suc _) zero    = Unit
Dif (suc m) (suc n) = Dif m n

Apart : Cell → Cell → Type₀                       -- PRIMITIVE
Apart (reg a) (reg b) = Dif (regIx a) (regIx b)
Apart (reg _) (mem _) = Unit
Apart (mem _) (reg _) = Unit
Apart (mem a) (mem b) = Dif a b

-- apartness refutes the Bool-valued equality `setR`/`setM` branch on
dif-neq : (m n : ℕ) → Dif m n → eqℕ m n Eq.≡ false
dif-neq zero    zero    ()
dif-neq zero    (suc n) _ = Eq.refl
dif-neq (suc m) zero    _ = Eq.refl
dif-neq (suc m) (suc n) d = dif-neq m n d

natCases : (m n : ℕ) → (m Eq.≡ n) ⊎ Dif m n
natCases zero    zero    = inl Eq.refl
natCases zero    (suc n) = inr tt
natCases (suc m) zero    = inr tt
natCases (suc m) (suc n) = go (natCases m n)
  where
  go : (m Eq.≡ n) ⊎ Dif m n → (suc m Eq.≡ suc n) ⊎ Dif m n
  go (inl e) = inl (Eq.ap suc e)
  go (inr d) = inr d

-- PRIMITIVE: the five registers, decided.  Twenty-five clauses, each
-- `inl Eq.refl` or `inr tt`; there is nothing to factor.
regCases : (a b : Reg) → (a Eq.≡ b) ⊎ Dif (regIx a) (regIx b)
regCases w0  w0  = inl Eq.refl
regCases w0  w9  = inr tt
regCases w0  w10 = inr tt
regCases w0  x19 = inr tt
regCases w0  x20 = inr tt
regCases w9  w0  = inr tt
regCases w9  w9  = inl Eq.refl
regCases w9  w10 = inr tt
regCases w9  x19 = inr tt
regCases w9  x20 = inr tt
regCases w10 w0  = inr tt
regCases w10 w9  = inr tt
regCases w10 w10 = inl Eq.refl
regCases w10 x19 = inr tt
regCases w10 x20 = inr tt
regCases x19 w0  = inr tt
regCases x19 w9  = inr tt
regCases x19 w10 = inr tt
regCases x19 x19 = inl Eq.refl
regCases x19 x20 = inr tt
regCases x20 w0  = inr tt
regCases x20 w9  = inr tt
regCases x20 w10 = inr tt
regCases x20 x19 = inr tt
regCases x20 x20 = inl Eq.refl

cellCases : (c d : Cell) → (c Eq.≡ d) ⊎ Apart c d
cellCases (reg a) (reg b) = go (regCases a b)
  where
  go : (a Eq.≡ b) ⊎ Dif (regIx a) (regIx b)
     → (reg a Eq.≡ reg b) ⊎ Dif (regIx a) (regIx b)
  go (inl e) = inl (Eq.ap reg e)
  go (inr d) = inr d
cellCases (reg a) (mem b) = inr tt
cellCases (mem a) (reg b) = inr tt
cellCases (mem a) (mem b) = go (natCases a b)
  where
  go : (a Eq.≡ b) ⊎ Dif a b → (mem a Eq.≡ mem b) ⊎ Dif a b
  go (inl e) = inl (Eq.ap mem e)
  go (inr d) = inr d

-- ==================================================================
-- §2  PARTIAL STATES, AND `Join`.
-- ==================================================================

PSt : Type₀
PSt = Cell → Maybe Word

IsJ : Maybe Word → Type₀                          -- PRIMITIVE
IsJ nothing  = ⊥
IsJ (just _) = Unit

IsN : Maybe Word → Type₀                          -- PRIMITIVE
IsN nothing  = Unit
IsN (just _) = ⊥

isNJ : (m : Maybe Word) → IsN m → IsJ m → ⊥
isNJ nothing  _  ()
isNJ (just _) () _

isJ-val : (m : Maybe Word) → IsJ m → Σ[ x ∈ Word ] (m Eq.≡ just x)
isJ-val nothing  ()
isJ-val (just x) _ = x , Eq.refl

just-inj : {a b : Word} → just a Eq.≡ just b → a Eq.≡ b
just-inj Eq.refl = Eq.refl

-- THE PARTIALITY CONDITION.  `Join m₁ m₂ m` -- "m is the disjoint union
-- of m₁ and m₂ at this cell".  NEVER both `just`.
Join : Maybe Word → Maybe Word → Maybe Word → Type₀   -- PRIMITIVE
Join nothing  nothing  nothing  = Unit
Join nothing  nothing  (just _) = ⊥
Join nothing  (just y) nothing  = ⊥
Join nothing  (just y) (just z) = y Eq.≡ z
Join (just x) nothing  nothing  = ⊥
Join (just x) nothing  (just z) = x Eq.≡ z
Join (just _) (just _) _        = ⊥

jnR : (m : Maybe Word) → Join m nothing m
jnR nothing  = tt
jnR (just x) = Eq.refl

jnL : (m : Maybe Word) → Join nothing m m
jnL nothing  = tt
jnL (just y) = Eq.refl

join-noneR : (m₁ m : Maybe Word) → Join m₁ nothing m → m₁ Eq.≡ m
join-noneR nothing  nothing  _ = Eq.refl
join-noneR nothing  (just z) ()
join-noneR (just x) nothing  ()
join-noneR (just x) (just z) e = Eq.ap just e

join-justR : (m₁ m : Maybe Word) (y : Word) → Join m₁ (just y) m
           → (m₁ Eq.≡ nothing) × (m Eq.≡ just y)
join-justR nothing  nothing  y ()
join-justR nothing  (just z) y e = Eq.refl , Eq.ap just (Eq.sym e)
join-justR (just x) m        y ()

join-subL : (m₂ m : Maybe Word) (x : Word) → Join (just x) m₂ m → m Eq.≡ just x
join-subL nothing  nothing  x ()
join-subL nothing  (just z) x e = Eq.ap just (Eq.sym e)
join-subL (just _) m        x ()

join-ownN : (m₁ m₂ m : Maybe Word) → Join m₁ m₂ m → IsJ m₁ → IsN m₂
join-ownN nothing  m₂        m jj ()
join-ownN (just _) nothing   m jj _ = tt
join-ownN (just _) (just _)  m jj _ = jj

-- ==================================================================
-- §3  THE PROMODEL.
-- ==================================================================

StSplit : (o : MonOp) → PSt → Type₀              -- PRIMITIVE
StSplit nilop σ = (c : Cell) → IsN (σ c)
StSplit appop σ =
  Σ[ σ₁ ∈ PSt ] Σ[ σ₂ ∈ PSt ] ((c : Cell) → Join (σ₁ c) (σ₂ c) (σ c))

StParts : (o : MonOp) (σ : PSt) → StSplit o σ → MonAr o → PSt
StParts nilop σ sp ()                             -- PRIMITIVE
StParts appop σ (σ₁ , σ₂ , _) = boolΠ {M = λ _ → PSt} σ₁ σ₂

stFib : Fibered monoidSig ℓ-zero ℓ-zero
stFib .carrier _ = PSt
stFib .Split     = StSplit
stFib .parts     = StParts

-- ------------------------------------------------------------------
-- IT IS A PROMODEL AND NOT A MODEL, AND THAT IS THE POINT.
--
-- `LaxPoint` asks for a TOTAL join: an operation `op` together with the
-- fact that every tuple splits its own composite AT that tuple.  A
-- partial map has no such join -- `σ ∗ σ` is undefined whenever `σ` owns
-- anything -- and the refutation is the one-cell resource, exactly as
-- `Heap.Base`'s `#-self` is.
--
-- So this is `Field`/`Heap`'s situation and not `Bags`': the multiplic-
-- atives (`⊗ˢ`, `⊸ˢ`, `⊸ᶠ`) and every additive survive, since
-- `FibNotation` and `RulesF` never mention `LaxPoint`; what does NOT
-- survive is `Bridge` (`⊗ˢ ≅ ⊗[ o ]`) and anything asking for `Honest`.
-- Nothing in this file wants either.
-- ------------------------------------------------------------------

none : PSt
none _ = nothing

-- the one-cell resource `reg w9 |-> v`
one9 : Word → PSt
one9 v (reg w0)  = nothing
one9 v (reg w9)  = just v
one9 v (reg w10) = nothing
one9 v (reg x19) = nothing
one9 v (reg x20) = nothing
one9 v (mem _)   = nothing

noPoint : LaxPoint stFib → ⊥
noPoint P = both
  where
  -- the SAME one-cell resource in both slots
  m⃗ : Bool → PSt
  m⃗ _ = one9 0

  sp : StSplit appop (P .op appop m⃗)
  sp = P .split appop m⃗

  ps : StParts appop (P .op appop m⃗) sp ≡ m⃗
  ps = P .parts-split appop m⃗

  both : ⊥
  both = transport
           (λ i → Join (ps i true (reg w9)) (ps i false (reg w9))
                       (P .op appop m⃗ (reg w9)))
           (sp .snd .snd (reg w9))

-- sub-state facts, read off `Join`
subJust : {σ₁ σ₂ σ : PSt} → ((c : Cell) → Join (σ₁ c) (σ₂ c) (σ c))
        → (c : Cell) (x : Word) → σ₁ c Eq.≡ just x → σ c Eq.≡ just x
subJust {σ₁} {σ₂} {σ} j c x e =
  join-subL (σ₂ c) (σ c) x (Eq.transport (λ m → Join m (σ₂ c) (σ c)) e (j c))

-- ==================================================================
-- §4  READS, WRITES, AND THE PER-INSTRUCTION COMMANDS.
--
-- `Rd?` is the read: if the cell is owned it holds this value, and
-- otherwise the value is UNCONSTRAINED.  So an instruction's footprint
-- is its WRITE set, and a cell that is only read may live in the frame.
-- ==================================================================

Own : PSt → Cell → Type₀
Own σ c = IsJ (σ c)

Rd : PSt → Cell → Word → Type₀
Rd σ c v = σ c Eq.≡ just v

Rd? : PSt → Cell → Word → Type₀
Rd? σ c v = IsJ (σ c) → σ c Eq.≡ just v

-- one write, at a cell that must be OWNED (so the domain is preserved)
Wr1 : Cell → Word → PSt → PSt → Type₀
Wr1 c v σ σ' =
  Own σ c × (σ' c Eq.≡ just v)
          × ((d : Cell) → Apart d c → σ' d Eq.≡ σ d)

-- two writes, at APART cells.  `strPost` and `ldrPre` are the two
-- instructions that write twice.
Wr2 : Cell → Word → Cell → Word → PSt → PSt → Type₀
Wr2 c v e u σ σ' =
  Own σ c × Own σ e × Apart c e
  × (σ' c Eq.≡ just v) × (σ' e Eq.≡ just u)
  × ((d : Cell) → Apart d c → Apart d e → σ' d Eq.≡ σ d)

-- PRIMITIVE (phase 1): the machine, as a command on partial states.
-- Compare `exec1`, clause for clause.
stepC : Instr → PSt → PSt → Type₀
stepC (movI d n)      σ σ' = Wr1 (reg d) n σ σ'
stepC (movR d n)      σ σ' =
  Σ[ x ∈ Word ] (Rd? σ (reg n) x × Wr1 (reg d) x σ σ')
stepC (addR d a b)    σ σ' =
  Σ[ x ∈ Word ] Σ[ y ∈ Word ]
    (Rd? σ (reg a) x × Rd? σ (reg b) y × Wr1 (reg d) (x + y) σ σ')
stepC (addI d n k)    σ σ' =
  Σ[ x ∈ Word ] (Rd? σ (reg n) x × Wr1 (reg d) (k + x) σ σ')
stepC (ldrO t n k)    σ σ' =
  Σ[ x ∈ Word ] Σ[ v ∈ Word ]
    (Rd? σ (reg n) x × Rd? σ (mem (x + k)) v × Wr1 (reg t) v σ σ')
stepC (strO t n k)    σ σ' =
  Σ[ x ∈ Word ] Σ[ v ∈ Word ]
    (Rd? σ (reg n) x × Rd? σ (reg t) v × Wr1 (mem (x + k)) v σ σ')
stepC (strPost t n k) σ σ' =
  Σ[ x ∈ Word ] Σ[ v ∈ Word ]
    (Rd? σ (reg n) x × Rd? σ (reg t) v × Wr2 (mem x) v (reg n) (k + x) σ σ')
stepC (ldrPre t n k)  σ σ' =
  Σ[ x ∈ Word ] Σ[ v ∈ Word ]
    (Rd? σ (reg n) x × Rd? σ (mem (sub x k)) v
     × Wr2 (reg n) (sub x k) (reg t) v σ σ')

-- ==================================================================
-- §5  AND HERE IS THE ENTIRE INSTANTIATION.
--
-- `Cmd`, `wp`, `∗`, `emp`, `Local`, `frame-wp`, `frameRuleCmd`, `sem`,
-- `seq∷`, `instrRule`, `local-sem`, ... all arrive.
-- ==================================================================

open import ISA.Program stFib Instr stepC public

-- ==================================================================
-- §6  AGREEMENT WITH THE REAL MACHINE.
--
-- On a TOTAL state every cell is owned, so `Rd?` is a genuine read and
-- `stepC` is `exec1`.  This is what makes the promodel a model OF
-- AArch64 rather than of something else.
-- ==================================================================

tot : St → PSt
tot s (reg r) = just (rg s r)
tot s (mem a) = just (mm s a)

totWrR : (r : Reg) (v : Word) (ρ : Regs) (μ : Mem)
       → Wr1 (reg r) v (tot (ρ , μ)) (tot (setR r v ρ , μ))
totWrR r v ρ μ = tt , Eq.ap just (setR-hit r v ρ) , ms
  where
  ms : (d : Cell) → Apart d (reg r)
     → tot (setR r v ρ , μ) d Eq.≡ tot (ρ , μ) d
  ms (reg q) a = Eq.ap (λ b → just (ifB b v (ρ q))) (dif-neq (regIx q) (regIx r) a)
  ms (mem c) a = Eq.refl

totWrM : (a v : Word) (ρ : Regs) (μ : Mem)
       → Wr1 (mem a) v (tot (ρ , μ)) (tot (ρ , setM a v μ))
totWrM a v ρ μ = tt , Eq.ap just (setM-hit a v μ) , ms
  where
  ms : (d : Cell) → Apart d (mem a)
     → tot (ρ , setM a v μ) d Eq.≡ tot (ρ , μ) d
  ms (reg q) p = Eq.refl
  ms (mem c) p = Eq.ap (λ b → just (ifB b v (μ c))) (dif-neq c a p)

-- `ldrPre t n k` writes BOTH `reg n` and `reg t`; the model asks for
-- them to be apart, which the compiler's `ldrPre w9 x20 16` satisfies.
-- Every other instruction has no side condition.
OKI : Instr → Type₀
OKI (movI _ _)     = Unit
OKI (movR _ _)     = Unit
OKI (addR _ _ _)   = Unit
OKI (addI _ _ _)   = Unit
OKI (ldrO _ _ _)   = Unit
OKI (strO _ _ _)   = Unit
OKI (strPost _ _ _) = Unit
OKI (ldrPre t n _) = Apart (reg n) (reg t)

OKP : Program → Type₀
OKP []      = Unit
OKP (i ∷ p) = OKI i × OKP p

-- THE AGREEMENT THEOREM.
stepC-tot : (i : Instr) → OKI i → (ρ : Regs) (μ : Mem)
          → stepC i (tot (ρ , μ)) (tot (exec1 i (ρ , μ)))
stepC-tot (movI d n)   _ ρ μ = totWrR d n ρ μ
stepC-tot (movR d n)   _ ρ μ = ρ n , (λ _ → Eq.refl) , totWrR d (ρ n) ρ μ
stepC-tot (addR d a b) _ ρ μ =
  ρ a , ρ b , (λ _ → Eq.refl) , (λ _ → Eq.refl) , totWrR d (ρ a + ρ b) ρ μ
stepC-tot (addI d n k) _ ρ μ = ρ n , (λ _ → Eq.refl) , totWrR d (k + ρ n) ρ μ
stepC-tot (ldrO t n k) _ ρ μ =
  ρ n , μ (ρ n + k) , (λ _ → Eq.refl) , (λ _ → Eq.refl) , totWrR t (μ (ρ n + k)) ρ μ
stepC-tot (strO t n k) _ ρ μ =
  ρ n , ρ t , (λ _ → Eq.refl) , (λ _ → Eq.refl) , totWrM (ρ n + k) (ρ t) ρ μ
stepC-tot (strPost t n k) _ ρ μ =
  ρ n , ρ t , (λ _ → Eq.refl) , (λ _ → Eq.refl)
  , ( tt , tt , tt
    , Eq.ap just (setM-hit (ρ n) (ρ t) μ)
    , Eq.ap just (setR-hit n (k + ρ n) ρ)
    , ms )
  where
  ms : (d : Cell) → Apart d (mem (ρ n)) → Apart d (reg n)
     → tot (setR n (k + ρ n) ρ , setM (ρ n) (ρ t) μ) d Eq.≡ tot (ρ , μ) d
  ms (reg q) _ b = Eq.ap (λ z → just (ifB z (k + ρ n) (ρ q))) (dif-neq (regIx q) (regIx n) b)
  ms (mem c) a _ = Eq.ap (λ z → just (ifB z (ρ t) (μ c))) (dif-neq c (ρ n) a)
stepC-tot (ldrPre t n k) ok ρ μ =
  ρ n , μ (sub (ρ n) k) , (λ _ → Eq.refl) , (λ _ → Eq.refl)
  , ( tt , tt , ok
    , ( Eq.ap (λ z → just (ifB z (μ (sub (ρ n) k)) (setR n (sub (ρ n) k) ρ n)))
              (dif-neq (regIx n) (regIx t) ok)
        Eq.∙ Eq.ap just (setR-hit n (sub (ρ n) k) ρ) )
    , Eq.ap just (setR-hit t (μ (sub (ρ n) k)) (setR n (sub (ρ n) k) ρ))
    , ms )
  where
  ms : (d : Cell) → Apart d (reg n) → Apart d (reg t)
     → tot (setR t (μ (sub (ρ n) k)) (setR n (sub (ρ n) k) ρ) , μ) d
       Eq.≡ tot (ρ , μ) d
  ms (reg q) a b =
    Eq.ap (λ z → just (ifB z (μ (sub (ρ n) k)) (ifB (eqR q n) (sub (ρ n) k) (ρ q))))
          (dif-neq (regIx q) (regIx t) b)
    Eq.∙ Eq.ap (λ z → just (ifB z (sub (ρ n) k) (ρ q))) (dif-neq (regIx q) (regIx n) a)
  ms (mem c) a b = Eq.refl

-- ... and therefore `sem` on total states IS `exec`.
sem-tot : (p : Program) → OKP p → (s : St) → sem p (tot s) (tot (exec p s))
sem-tot []      _        s = Eq.refl
sem-tot (i ∷ p) (ok , k) s =
  tot (exec1 i s) , stepC-tot i ok (rg s) (mm s) , sem-tot p k (exec1 i s)

-- ==================================================================
-- §7  `Local` IS FALSE HERE, AND HERE IS THE COUNTEREXAMPLE.
--
-- `ISA.Machine.Local` has no safety side condition, so it demands that
-- a command run on EVERY left part of EVERY splitting -- including the
-- empty one.  A write cannot do that: writing needs ownership.
-- ==================================================================

-- ... split with EVERYTHING in the frame
one9Split : (v : Word) → StSplit appop (one9 v)
one9Split v = none , one9 v , λ c → jnL (one9 v c)

one9Step : (v w : Word) → stepC (movI w9 w) (one9 v) (one9 w)
one9Step v w = tt , Eq.refl , ms
  where
  ms : (d : Cell) → Apart d (reg w9) → one9 w d Eq.≡ one9 v d
  ms (reg w0)  _ = Eq.refl
  ms (reg w9)  ()
  ms (reg w10) _ = Eq.refl
  ms (reg x19) _ = Eq.refl
  ms (reg x20) _ = Eq.refl
  ms (mem _)   _ = Eq.refl

-- THE COUNTEREXAMPLE.  `Local` would make `movI w9 5` run on the empty
-- resource, whose first obligation is owning `reg w9` there -- which is
-- `IsJ nothing`, i.e. `⊥`.
no-Local-movI : Local (stepC (movI w9 5)) → ⊥
no-Local-movI loc =
  loc (one9 0) (one9Split 0) (one9 5) (one9Step 0 5) .snd .fst .fst

-- ==================================================================
-- §8  LOCALITY, WITH THE SAFETY SIDE CONDITION.
--
-- `LocalOn S c` is `ISA.Machine.Local` with ONE extra hypothesis: the
-- command is safe -- in the sense recorded by `S` -- on the small part.
-- Everything below is the corresponding rule from `ISA.Machine` with
-- that hypothesis threaded, and nothing else changes.
-- ==================================================================

LocalOn : Gr → Cmd → Type₀
LocalOn S c =
  (σ : PSt) (sp : stFib .Split appop σ) (σ' : PSt)
  → S (stFib .parts appop σ sp true)
  → c σ σ'
  → Σ[ sp' ∈ stFib .Split appop σ' ]
      ( c (stFib .parts appop σ sp true) (stFib .parts appop σ' sp' true)
      × (stFib .parts appop σ' sp' false Eq.≡ stFib .parts appop σ sp false) )

-- `Local` is the special case where safety says nothing
Local→LocalOn : (c : Cmd) → Local c → (S : Gr) → LocalOn S c
Local→LocalOn c loc S σ sp σ' _ r = loc σ sp σ' r

localOn-weaken : {S T : Gr} (c : Cmd) → T ⊢ S → LocalOn S c → LocalOn T c
localOn-weaken c f loc σ sp σ' t r = loc σ sp σ' (f _ t) r

localOn-skip : (S : Gr) → LocalOn S skip
localOn-skip S h sp .h _ Eq.refl = sp , Eq.refl , Eq.refl

-- THE COMPOSITE'S SAFETY IS `S & wp c T`: "safe now, and safe after
-- every step".  `ISA.Toy`'s header predicted exactly this shape; what
-- it did not say is that the second conjunct needs no new notion, being
-- literally the weakest precondition.
localOn-comp : (S T : Gr) (c d : Cmd)
             → LocalOn S c → LocalOn T d → LocalOn (S & wp c T) (c ⨟ d)
localOn-comp S T c d lc ld σ sp σ'' (s , wt) (m , cm , dm) =
  ld' .fst
  , (stFib .parts appop m (lc' .fst) true , lc' .snd .fst , ld' .snd .fst)
  , eqTrans (ld' .snd .snd) (lc' .snd .snd)
  where
  lc' = lc σ sp m s cm
  ld' = ld m (lc' .fst) σ'' (wt _ (lc' .snd .fst)) dm

-- THE FRAME RULE.  `ISA.Machine.frame-wp` verbatim, with `k true`
-- carrying safety alongside the weakest precondition.
frameOn-wp : (S : Gr) (c : Cmd) → LocalOn S c → (Q R : Gr)
           → ((S & wp c Q) ∗ R) ⊢ wp c (Q ∗ R)
frameOn-wp S c loc Q R =
  ⊗ˢ-E appop {A = boolΠ {M = λ _ → Gr} (S & wp c Q) R}
    (λ σ sp k σ' cs →
      let l   = loc σ sp σ' (k true .fst) cs
          sp' = l .fst
      in ⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} Q R} σ' sp'
           (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} Q R a
                               (stFib .parts appop σ' sp' a)}
                  (k true .snd (stFib .parts appop σ' sp' true) (l .snd .fst))
                  (coeG R (Eq.sym (l .snd .snd)) (k false))))

-- ... and as a rule about triples
frameRuleOn : (S R : Gr) (c : Cmd) → LocalOn S c → {P Q : Gr}
            → P ⊢ (S & wp c Q) → (P ∗ R) ⊢ wp c (Q ∗ R)
frameRuleOn S R c loc {P} {Q} t = frameOn-wp S c loc Q R ∘g ∗-map R t

-- ==================================================================
-- §9  THE TRANSFER OF A SPLITTING ACROSS A WRITE.
--
-- The construction is one line -- keep the frame `σ₂` LITERALLY, and
-- take the new small part to be `σ'` masked by the frame's domain.  The
-- frame slot of the result is then `σ₂` on the nose, which is why
-- `Local`'s third component is `Eq.refl` and no funext appears.
-- ==================================================================

maskM : Maybe Word → Maybe Word → Maybe Word
maskM (just _) _ = nothing
maskM nothing  t = t

sml : PSt → PSt → PSt
sml φ τ d = maskM (φ d) (τ d)

maskM-free : (m t : Maybe Word) → IsN m → maskM m t Eq.≡ t
maskM-free nothing  t _  = Eq.refl
maskM-free (just _) t ()

mask-keep : (m₁ m₂ m t : Maybe Word) → Join m₁ m₂ m → t Eq.≡ m → maskM m₂ t Eq.≡ m₁
mask-keep m₁ nothing  m t jj e = e Eq.∙ Eq.sym (join-noneR m₁ m jj)
mask-keep m₁ (just y) m t jj e = Eq.sym (join-justR m₁ m y jj .fst)

mask-Join : (m₁ m₂ m t : Maybe Word) → Join m₁ m₂ m → (IsJ m₂ → t Eq.≡ m)
          → Join (maskM m₂ t) m₂ t
mask-Join m₁ nothing  m t jj ag = jnR t
mask-Join m₁ (just y) m t jj ag =
  Eq.transport (λ z → Join nothing (just y) z)
               (Eq.sym (ag tt Eq.∙ join-justR m₁ m y jj .snd)) Eq.refl

tSplit : (σ σ₁ σ₂ : PSt) (j : (c : Cell) → Join (σ₁ c) (σ₂ c) (σ c)) (σ' : PSt)
       → ((d : Cell) → IsJ (σ₂ d) → σ' d Eq.≡ σ d)
       → StSplit appop σ'
tSplit σ σ₁ σ₂ j σ' ag =
  sml σ₂ σ' , σ₂ , λ c → mask-Join (σ₁ c) (σ₂ c) (σ c) (σ' c) (j c) (ag c)

-- the frame is untouched, because the written cell is owned by the
-- SMALL part and a splitting never gives one cell to both
agree1 : (σ σ₁ σ₂ : PSt) (j : (c : Cell) → Join (σ₁ c) (σ₂ c) (σ c)) (σ' : PSt)
         (c : Cell) (v : Word) → Wr1 c v σ σ' → Own σ₁ c
       → (d : Cell) → IsJ (σ₂ d) → σ' d Eq.≡ σ d
agree1 σ σ₁ σ₂ j σ' c v (_ , _ , miss) own d ij = go (cellCases d c)
  where
  go : (d Eq.≡ c) ⊎ Apart d c → σ' d Eq.≡ σ d
  go (inl e) = E.rec (isNJ (σ₂ c) (join-ownN (σ₁ c) (σ₂ c) (σ c) (j c) own)
                            (Eq.transport (λ z → IsJ (σ₂ z)) e ij))
  go (inr a) = miss d a

wr1-small : (σ σ₁ σ₂ : PSt) (j : (c : Cell) → Join (σ₁ c) (σ₂ c) (σ c)) (σ' : PSt)
            (c : Cell) (v : Word) → Wr1 c v σ σ' → Own σ₁ c
          → Wr1 c v σ₁ (sml σ₂ σ')
wr1-small σ σ₁ σ₂ j σ' c v (_ , hit , miss) own =
  own
  , (maskM-free (σ₂ c) (σ' c) (join-ownN (σ₁ c) (σ₂ c) (σ c) (j c) own) Eq.∙ hit)
  , λ d a → mask-keep (σ₁ d) (σ₂ d) (σ d) (σ' d) (j d) (miss d a)

agree2 : (σ σ₁ σ₂ : PSt) (j : (c : Cell) → Join (σ₁ c) (σ₂ c) (σ c)) (σ' : PSt)
         (c e : Cell) (v u : Word) → Wr2 c v e u σ σ' → Own σ₁ c → Own σ₁ e
       → (d : Cell) → IsJ (σ₂ d) → σ' d Eq.≡ σ d
agree2 σ σ₁ σ₂ j σ' c e v u (_ , _ , _ , _ , _ , miss) oc oe d ij =
  go (cellCases d c) (cellCases d e)
  where
  go : (d Eq.≡ c) ⊎ Apart d c → (d Eq.≡ e) ⊎ Apart d e → σ' d Eq.≡ σ d
  go (inl p) _ = E.rec (isNJ (σ₂ c) (join-ownN (σ₁ c) (σ₂ c) (σ c) (j c) oc)
                              (Eq.transport (λ z → IsJ (σ₂ z)) p ij))
  go (inr a) (inl q) = E.rec (isNJ (σ₂ e) (join-ownN (σ₁ e) (σ₂ e) (σ e) (j e) oe)
                                    (Eq.transport (λ z → IsJ (σ₂ z)) q ij))
  go (inr a) (inr b) = miss d a b

wr2-small : (σ σ₁ σ₂ : PSt) (j : (c : Cell) → Join (σ₁ c) (σ₂ c) (σ c)) (σ' : PSt)
            (c e : Cell) (v u : Word) → Wr2 c v e u σ σ' → Own σ₁ c → Own σ₁ e
          → Wr2 c v e u σ₁ (sml σ₂ σ')
wr2-small σ σ₁ σ₂ j σ' c e v u (_ , _ , ap , hc , he , miss) oc oe =
  oc , oe , ap
  , (maskM-free (σ₂ c) (σ' c) (join-ownN (σ₁ c) (σ₂ c) (σ c) (j c) oc) Eq.∙ hc)
  , (maskM-free (σ₂ e) (σ' e) (join-ownN (σ₁ e) (σ₂ e) (σ e) (j e) oe) Eq.∙ he)
  , λ d a b → mask-keep (σ₁ d) (σ₂ d) (σ d) (σ' d) (j d) (miss d a b)

-- a read that the small part owns sees what the whole state sees
subRd? : {σ₁ σ₂ σ : PSt} → ((c : Cell) → Join (σ₁ c) (σ₂ c) (σ c))
       → (c : Cell) (v : Word) → Rd? σ c v → Rd? σ₁ c v
subRd? {σ₁} {σ₂} {σ} j c v r ij =
  isJ-val (σ₁ c) ij .snd
  Eq.∙ Eq.ap just (just-inj
        (Eq.sym (subJust j c (isJ-val (σ₁ c) ij .fst) (isJ-val (σ₁ c) ij .snd))
         Eq.∙ r (Eq.transport IsJ
                  (Eq.sym (subJust j c (isJ-val (σ₁ c) ij .fst)
                                       (isJ-val (σ₁ c) ij .snd))) tt)))

agreeRd : {σ₁ σ₂ σ : PSt} (j : (c : Cell) → Join (σ₁ c) (σ₂ c) (σ c))
        → (c : Cell) (x y : Word) → Rd σ₁ c x → Rd? σ c y → x Eq.≡ y
agreeRd {σ₁} {σ₂} {σ} j c x y r1 r2 =
  just-inj (Eq.sym (subJust j c x r1)
            Eq.∙ r2 (Eq.transport IsJ (Eq.sym (subJust j c x r1)) tt))

-- ==================================================================
-- §10  THE PER-INSTRUCTION SAFETY, AND LOCALITY.
--
-- `OwnI i` names exactly the cells `i` WRITES (plus, where the write
-- address is computed, the register that names it).  Reads do not
-- appear: `Rd?` made them frame-tolerant.
-- ==================================================================

OwnI : Instr → Gr
OwnI (movI d n)      σ = Own σ (reg d)
OwnI (movR d n)      σ = Own σ (reg d)
OwnI (addR d a b)    σ = Own σ (reg d)
OwnI (addI d n k)    σ = Own σ (reg d)
OwnI (ldrO t n k)    σ = Own σ (reg t)
OwnI (strO t n k)    σ = Σ[ x ∈ Word ] (Rd σ (reg n) x × Own σ (mem (x + k)))
OwnI (strPost t n k) σ = Σ[ x ∈ Word ] (Rd σ (reg n) x × Own σ (mem x))
OwnI (ldrPre t n k)  σ =
  Σ[ x ∈ Word ] (Rd σ (reg n) x × Own σ (reg t) × Apart (reg n) (reg t))

localI : (i : Instr) → LocalOn (OwnI i) (stepC i)
localI (movI d n) σ (σ₁ , σ₂ , j) σ' own w =
  tSplit σ σ₁ σ₂ j σ' (agree1 σ σ₁ σ₂ j σ' (reg d) n w own)
  , wr1-small σ σ₁ σ₂ j σ' (reg d) n w own
  , Eq.refl
localI (movR d n) σ (σ₁ , σ₂ , j) σ' own (x , rn , w) =
  tSplit σ σ₁ σ₂ j σ' (agree1 σ σ₁ σ₂ j σ' (reg d) x w own)
  , ( x , subRd? j (reg n) x rn
    , wr1-small σ σ₁ σ₂ j σ' (reg d) x w own )
  , Eq.refl
localI (addR d a b) σ (σ₁ , σ₂ , j) σ' own (x , y , ra , rb , w) =
  tSplit σ σ₁ σ₂ j σ' (agree1 σ σ₁ σ₂ j σ' (reg d) (x + y) w own)
  , ( x , y , subRd? j (reg a) x ra , subRd? j (reg b) y rb
    , wr1-small σ σ₁ σ₂ j σ' (reg d) (x + y) w own )
  , Eq.refl
localI (addI d n k) σ (σ₁ , σ₂ , j) σ' own (x , rn , w) =
  tSplit σ σ₁ σ₂ j σ' (agree1 σ σ₁ σ₂ j σ' (reg d) (k + x) w own)
  , ( x , subRd? j (reg n) x rn
    , wr1-small σ σ₁ σ₂ j σ' (reg d) (k + x) w own )
  , Eq.refl
localI (ldrO t n k) σ (σ₁ , σ₂ , j) σ' own (x , v , rn , rv , w) =
  tSplit σ σ₁ σ₂ j σ' (agree1 σ σ₁ σ₂ j σ' (reg t) v w own)
  , ( x , v , subRd? j (reg n) x rn , subRd? j (mem (x + k)) v rv
    , wr1-small σ σ₁ σ₂ j σ' (reg t) v w own )
  , Eq.refl
localI (strO t n k) σ (σ₁ , σ₂ , j) σ' (x₁ , rd₁ , om) (x , v , rn , rv , w) =
  tSplit σ σ₁ σ₂ j σ' (agree1 σ σ₁ σ₂ j σ' (mem (x + k)) v w om')
  , ( x , v , subRd? j (reg n) x rn , subRd? j (reg t) v rv
    , wr1-small σ σ₁ σ₂ j σ' (mem (x + k)) v w om' )
  , Eq.refl
  where
  om' : Own σ₁ (mem (x + k))
  om' = Eq.transport (λ z → Own σ₁ (mem (z + k))) (agreeRd j (reg n) x₁ x rd₁ rn) om
localI (strPost t n k) σ (σ₁ , σ₂ , j) σ' (x₁ , rd₁ , om) (x , v , rn , rv , w) =
  tSplit σ σ₁ σ₂ j σ' (agree2 σ σ₁ σ₂ j σ' (mem x) (reg n) v (k + x) w om' on)
  , ( x , v , subRd? j (reg n) x rn , subRd? j (reg t) v rv
    , wr2-small σ σ₁ σ₂ j σ' (mem x) (reg n) v (k + x) w om' on )
  , Eq.refl
  where
  om' : Own σ₁ (mem x)
  om' = Eq.transport (λ z → Own σ₁ (mem z)) (agreeRd j (reg n) x₁ x rd₁ rn) om
  on : Own σ₁ (reg n)
  on = Eq.transport IsJ (Eq.sym rd₁) tt
localI (ldrPre t n k) σ (σ₁ , σ₂ , j) σ' (x₁ , rd₁ , ot , ap) (x , v , rn , rv , w) =
  tSplit σ σ₁ σ₂ j σ' (agree2 σ σ₁ σ₂ j σ' (reg n) (reg t) (sub x k) v w on ot)
  , ( x , v , subRd? j (reg n) x rn , subRd? j (mem (sub x k)) v rv
    , wr2-small σ σ₁ σ₂ j σ' (reg n) (reg t) (sub x k) v w on ot )
  , Eq.refl
  where
  on : Own σ₁ (reg n)
  on = Eq.transport IsJ (Eq.sym rd₁) tt

-- ==================================================================
-- §11  PROGRAMS.
--
-- The safety of a program is the same recursion the free-monoid
-- extension `sem` is, and locality lifts along it -- `ISA.Program`'s
-- `local-sem` with the safety argument threaded.
-- ==================================================================

SafeP : Program → Gr
SafeP []      = ⊤G
SafeP (i ∷ p) = OwnI i & wp (stepC i) (SafeP p)

localOn-sem : (p : Program) → LocalOn (SafeP p) (sem p)
localOn-sem []      = localOn-skip ⊤G
localOn-sem (i ∷ p) =
  localOn-comp (OwnI i) (SafeP p) (stepC i) (sem p) (localI i) (localOn-sem p)

-- THE FRAME RULE FOR A PROGRAM.  The per-instruction obligation is
-- `localI`; everything else was already generic.
frameProg : (R : Gr) (p : Program) {P Q : Gr}
          → P ⊢ (SafeP p & wp (sem p) Q) → (P ∗ R) ⊢ wp (sem p) (Q ∗ R)
frameProg R p = frameRuleOn (SafeP p) R (sem p) (localOn-sem p)

-- ==================================================================
-- §12  THE PAYOFF: `pLow` WITHOUT ARITHMETIC.
--
-- `frameLow` is the whole content of `AArch64Codegen`'s `pLow`, and it
-- is `localOn-sem` read at one cell: the frame slot of the output
-- splitting IS the frame slot of the input, so anything the program
-- does not own is unchanged -- no `setM-miss`, no `lt-neq`, no
-- induction over the expression.
-- ==================================================================

ltB : ℕ → ℕ → Bool
ltB _       zero    = false
ltB zero    (suc _) = true
ltB (suc m) (suc n) = ltB m n

lt-ltB : (m n : ℕ) → Lt m n → ltB m n Eq.≡ true
lt-ltB m       zero    ()
lt-ltB zero    (suc n) _ = Eq.refl
lt-ltB (suc m) (suc n) l = lt-ltB m n l

ltB-irrefl : (n : ℕ) → ltB n n Eq.≡ false
ltB-irrefl zero    = Eq.refl
ltB-irrefl (suc n) = ltB-irrefl n

ifM : Bool → Word → Maybe Word → Maybe Word
ifM true  v m = just v
ifM false v m = m

ifM-sub : (b : Bool) (v : Word) → IsJ (ifM b v nothing) → ifM b v nothing Eq.≡ just v
ifM-sub true  v _ = Eq.refl
ifM-sub false v ()

maskJoin : (m t : Maybe Word) → (IsJ m → m Eq.≡ t) → Join (maskM m t) m t
maskJoin nothing  t _ = jnR t
maskJoin (just x) t h = Eq.transport (λ z → Join nothing (just x) z) (h tt) Eq.refl

-- THE LOW REGION: memory strictly below `b`, and nothing else.
low : Word → St → PSt
low b s (reg _) = nothing
low b s (mem a) = ifM (ltB a b) (mm s a) nothing

-- ... and its complement inside the total state
hi : Word → St → PSt
hi b s d = maskM (low b s d) (tot s d)

lowSplit : (b : Word) (s : St) → StSplit appop (tot s)
lowSplit b s = hi b s , low b s , λ c → maskJoin (low b s c) (tot s c) (sb c)
  where
  sb : (c : Cell) → IsJ (low b s c) → low b s c Eq.≡ tot s c
  sb (reg r) ()
  sb (mem a) ij = ifM-sub (ltB a b) (mm s a) ij

-- THE GENERIC NON-INTERFERENCE THEOREM.  A program safe on the
-- complement of the low region cannot touch the low region.
frameLow : (p : Program) → OKP p → (b : Word) (s : St)
         → SafeP p (hi b s)
         → (a : Word) → Lt a b → mm (exec p s) a Eq.≡ mm s a
frameLow p ok b s saf a l = just-inj (join-justR _ _ (mm s a) jj .snd)
  where
  res = localOn-sem p (tot s) (lowSplit b s) (tot (exec p s)) saf (sem-tot p ok s)
  sp' = res .fst
  fr  = res .snd .snd

  jj : Join (sp' .fst (mem a)) (just (mm s a)) (just (mm (exec p s) a))
  jj = Eq.transport (λ m → Join (sp' .fst (mem a)) m (just (mm (exec p s) a)))
         ( Eq.ap (λ f → f (mem a)) fr
           Eq.∙ Eq.ap (λ z → ifM z (mm s a) nothing) (lt-ltB a b l) )
         (sp' .snd .snd (mem a))

-- ------------------------------------------------------------------
-- AND HERE IT IS AT A REAL MACRO.  `push9` is `AArch64Codegen`'s own
-- push; its footprint is three cells, so the low region is untouched --
-- which is `pLow` for the push, obtained by framing.
-- ------------------------------------------------------------------

open import Compile.ArithToARM.AArch64Codegen using (push9; addSeq; compile; Post; pLow)
open import Compile.ArithToARM.Base using (Exp; evar; elit; eadd)

push9-OK : OKP push9
push9-OK = tt , tt

push9Safe : (s : St) → SafeP push9 (hi (rg s x20) s)
push9Safe s =
  ( rg s x20 , Eq.refl
  , Eq.transport (λ z → IsJ (maskM (ifM z (mm s (rg s x20)) nothing)
                                   (just (mm s (rg s x20)))))
                 (Eq.sym (ltB-irrefl (rg s x20))) tt )
  , λ _ _ → tt

-- `pLow` FOR THE PUSH MACRO, FOR FREE.
push9Low : (s : St) (a : Word) → Lt a (rg s x20)
         → mm (exec push9 s) a Eq.≡ mm s a
push9Low s = frameLow push9 push9-OK (rg s x20) s (push9Safe s)

-- ==================================================================
-- §13  ... AND FOR THE WHOLE COMPILER.
--
-- `compileLow` is `AArch64Codegen`'s `Post.pLow` VERBATIM -- same
-- statement, same `Lt`, same `exec` -- but here it is a composite of
-- `frameLow`, and `frameLow` is `localOn-sem` read at one cell.  Not a
-- single `setM-miss` and not a single `lt-neq` occurs in its
-- derivation, where the hand proof spends one of each at every node of
-- the expression AND has to transport the stack pointer through both
-- subexpressions to do it.
--
-- What framing charges instead is `compileSafe`, and the exchange is
-- the whole point:
--
--     pLow  by hand    : "at every write, the address DIFFERS from a";
--                        a statement about memory CONTENTS, needing
--                        `setM-miss`, `lt-neq` and the arithmetic of
--                        `sub`, at every node.
--
--     compileSafe      : "every write is to a cell the program OWNS";
--                        a statement about the DOMAIN, Unit/⊥-valued,
--                        independent of what is stored, and never
--                        comparing one address with another.
--
-- The footprint `hi b s` is the right one and needs no cleverness: the
-- compiler writes only `w9`, `w10`, `x20` and stack memory (all owned),
-- and READS `x19` and the environment, which `Rd?` lets it do from the
-- FRAME.  Note in particular that `Sep` -- `AArch64Codegen`'s
-- separation hypothesis -- is NOT needed for `pLow`; the ownership
-- discipline replaces it, and `compileInv` below takes no hypothesis
-- about the environment at all.
--
-- One detail earns its keep.  `Inv base sp` anchors MEMORY ownership at
-- the incoming pointer `base` and tracks the CURRENT pointer `sp`
-- separately.  Anchoring at `sp` would be wrong in exactly one place --
-- a pop lowers the pointer, and the slot it lands on must still be
-- owned -- and that is the only subtlety in the induction.
-- ==================================================================

OKP-++ : (p q : Program) → OKP p → OKP q → OKP (p ++ q)
OKP-++ []      q _        kq = kq
OKP-++ (i ∷ p) q (o , kp) kq = o , OKP-++ p q kp kq

compileOK : ∀ {u} (e : Exp u) → OKP (compile e)
compileOK (evar so)     = tt , tt , tt
compileOK (elit _ n)    = tt , tt , tt
compileOK (eadd sp a b) =
  OKP-++ (compile a) (compile b ++ addSeq) (compileOK a)
    (OKP-++ (compile b) addSeq (compileOK b) (tt , tt , tt , tt , tt))

-- safety of a concatenation: safe now, and safe after the first block.
-- The same two monoid laws `ISA.Program.homSplit3` is.
SafeP-++ : (p q : Program) (σ : PSt)
         → SafeP p σ → wp (sem p) (SafeP q) σ → SafeP (p ++ q) σ
SafeP-++ []      q σ _        w = w σ Eq.refl
SafeP-++ (i ∷ p) q σ (o , wi) w =
  o , λ τ st → SafeP-++ p q τ (wi τ st) (λ υ sp → w υ (τ , st , sp))

-- ------------------------------------------------------------------
-- THE OWNERSHIP INVARIANT.  Note what it says and what it does not:
-- memory ownership is anchored at the INCOMING stack pointer `base` and
-- never moves, while the pointer `sp` is tracked separately.  That is
-- what lets a POP -- which lowers the pointer -- keep owning the slot
-- it lands on.  Nothing in it mentions a stored value.
-- ------------------------------------------------------------------

Ge : ℕ → ℕ → Type₀                                -- PRIMITIVE
Ge _       zero    = Unit
Ge zero    (suc _) = ⊥
Ge (suc m) (suc n) = Ge m n

ge-refl : (n : ℕ) → Ge n n
ge-refl zero    = tt
ge-refl (suc n) = ge-refl n

ge-sucR : (a b : ℕ) → Ge a (suc b) → Ge a b
ge-sucR zero    b       ()
ge-sucR (suc a) zero    _ = tt
ge-sucR (suc a) (suc b) g = ge-sucR a b g

ge-addR : (j a b : ℕ) → Ge a (j + b) → Ge a b
ge-addR zero    a b g = g
ge-addR (suc j) a b g = ge-addR j a b (ge-sucR a (j + b) g)

ge-sucL : (a b : ℕ) → Ge a b → Ge (suc a) b
ge-sucL a       zero    _  = tt
ge-sucL zero    (suc b) ()
ge-sucL (suc a) (suc b) g  = ge-sucL a b g

ge-addL : (j a b : ℕ) → Ge a b → Ge (j + a) b
ge-addL zero    a b g = g
ge-addL (suc j) a b g = ge-sucL (j + a) b (ge-addL j a b g)

ge-ltB : (a b : ℕ) → Ge a b → ltB a b Eq.≡ false
ge-ltB a       zero    _  = Eq.refl
ge-ltB zero    (suc b) ()
ge-ltB (suc a) (suc b) g  = ge-ltB a b g

Inv : Word → Word → Gr
Inv base sp σ =
  Own σ (reg w9) × Own σ (reg w10) × Rd σ (reg x20) sp
  × ((a : Word) → Ge a base → Own σ (mem a))

-- a write never shrinks the domain
own-Wr1 : (c : Cell) (v : Word) (σ τ : PSt) → Wr1 c v σ τ
        → (d : Cell) → Own σ d → Own τ d
own-Wr1 c v σ τ (_ , hit , miss) d o = go (cellCases d c)
  where
  go : (d Eq.≡ c) ⊎ Apart d c → Own τ d
  go (inl p) = Eq.transport (λ z → IsJ (τ z)) (Eq.sym p)
                            (Eq.transport IsJ (Eq.sym hit) tt)
  go (inr a) = Eq.transport IsJ (Eq.sym (miss d a)) o

own-Wr2 : (c e : Cell) (v u : Word) (σ τ : PSt) → Wr2 c v e u σ τ
        → (d : Cell) → Own σ d → Own τ d
own-Wr2 c e v u σ τ (_ , _ , _ , hc , he , miss) d o =
  go (cellCases d c) (cellCases d e)
  where
  go : (d Eq.≡ c) ⊎ Apart d c → (d Eq.≡ e) ⊎ Apart d e → Own τ d
  go (inl p) _ = Eq.transport (λ z → IsJ (τ z)) (Eq.sym p)
                              (Eq.transport IsJ (Eq.sym hc) tt)
  go (inr a) (inl q) = Eq.transport (λ z → IsJ (τ z)) (Eq.sym q)
                                    (Eq.transport IsJ (Eq.sym he) tt)
  go (inr a) (inr b) = Eq.transport IsJ (Eq.sym (miss d a b)) o

rdAgree : (σ : PSt) (c : Cell) (x y : Word) → Rd σ c x → Rd? σ c y → x Eq.≡ y
rdAgree σ c x y r1 r2 =
  just-inj (Eq.sym r1 Eq.∙ r2 (Eq.transport IsJ (Eq.sym r1) tt))

-- ------------------------------------------------------------------
-- THE INVARIANT UNDER EACH INSTRUCTION THE COMPILER EMITS.
-- ------------------------------------------------------------------

-- anything that writes only `w9` leaves the invariant alone
invW9 : (v base sp : Word) (σ τ : PSt) → Inv base sp σ → Wr1 (reg w9) v σ τ
      → Inv base sp τ
invW9 v base sp σ τ (o9 , o10 , rx , om) w =
  own-Wr1 (reg w9) v σ τ w (reg w9) o9
  , own-Wr1 (reg w9) v σ τ w (reg w10) o10
  , (w .snd .snd (reg x20) tt Eq.∙ rx)
  , λ a g → own-Wr1 (reg w9) v σ τ w (mem a) (om a g)

invMovI : (n base sp : Word) (σ : PSt) → Inv base sp σ
        → wp (stepC (movI w9 n)) (Inv base sp) σ
invMovI n base sp σ inv τ w = invW9 n base sp σ τ inv w

invLdrO : (k base sp : Word) (σ : PSt) → Inv base sp σ
        → wp (stepC (ldrO w9 x19 k)) (Inv base sp) σ
invLdrO k base sp σ inv τ (x , v , rn , rv , w) = invW9 v base sp σ τ inv w

invAddR : (base sp : Word) (σ : PSt) → Inv base sp σ
        → wp (stepC (addR w9 w10 w9)) (Inv base sp) σ
invAddR base sp σ inv τ (x , y , ra , rb , w) = invW9 (x + y) base sp σ τ inv w

-- the PUSH: `x20` advances by one slot, and the slot it wrote is still
-- owned because ownership is anchored at `base`
invPush : (base sp : Word) (σ : PSt) → Inv base sp σ
        → wp (stepC (strPost w9 x20 16)) (Inv base (16 + sp)) σ
invPush base sp σ (o9 , o10 , rx , om) τ (x , v , rn , rv , w) =
  own-Wr2 (mem x) (reg x20) v (16 + x) σ τ w (reg w9) o9
  , own-Wr2 (mem x) (reg x20) v (16 + x) σ τ w (reg w10) o10
  , Eq.transport (λ z → τ (reg x20) Eq.≡ just (16 + z))
                 (Eq.sym (rdAgree σ (reg x20) sp x rx rn))
                 (w .snd .snd .snd .snd .fst)
  , λ a g → own-Wr2 (mem x) (reg x20) v (16 + x) σ τ w (mem a) (om a g)

-- the two POPs.  `sub (16 + sp) 16` strips sixteen successors and
-- computes, so no arithmetic lemma is needed.
invPop9 : (base sp : Word) (σ : PSt) → Inv base (16 + sp) σ
        → wp (stepC (ldrPre w9 x20 16)) (Inv base sp) σ
invPop9 base sp σ (o9 , o10 , rx , om) τ (x , v , rn , rv , w) =
  Eq.transport IsJ (Eq.sym (w .snd .snd .snd .snd .fst)) tt
  , own-Wr2 (reg x20) (reg w9) (sub x 16) v σ τ w (reg w10) o10
  , Eq.transport (λ z → τ (reg x20) Eq.≡ just (sub z 16))
                 (Eq.sym (rdAgree σ (reg x20) (16 + sp) x rx rn))
                 (w .snd .snd .snd .fst)
  , λ a g → own-Wr2 (reg x20) (reg w9) (sub x 16) v σ τ w (mem a) (om a g)

invPop10 : (base sp : Word) (σ : PSt) → Inv base (16 + sp) σ
         → wp (stepC (ldrPre w10 x20 16)) (Inv base sp) σ
invPop10 base sp σ (o9 , o10 , rx , om) τ (x , v , rn , rv , w) =
  own-Wr2 (reg x20) (reg w10) (sub x 16) v σ τ w (reg w9) o9
  , Eq.transport IsJ (Eq.sym (w .snd .snd .snd .snd .fst)) tt
  , Eq.transport (λ z → τ (reg x20) Eq.≡ just (sub z 16))
                 (Eq.sym (rdAgree σ (reg x20) (16 + sp) x rx rn))
                 (w .snd .snd .snd .fst)
  , λ a g → own-Wr2 (reg x20) (reg w10) (sub x 16) v σ τ w (mem a) (om a g)

-- ------------------------------------------------------------------
-- THE TWO MACROS.
-- ------------------------------------------------------------------

pushSafe : (base sp : Word) (σ : PSt) → Ge sp base → Inv base sp σ → SafeP push9 σ
pushSafe base sp σ ge (o9 , o10 , rx , om) = (sp , rx , om sp ge) , λ _ _ → tt

pushWp : (base sp : Word) (σ : PSt) → Inv base sp σ
       → wp (sem push9) (Inv base (16 + sp)) σ
pushWp base sp σ inv σ' (τ , st , Eq.refl) = invPush base sp σ inv τ st

addSeqSafe : (base sp : Word) (σ : PSt) → Ge sp base
           → Inv base (16 + (16 + sp)) σ → SafeP addSeq σ
addSeqSafe base sp σ ge inv =
  ( 16 + (16 + sp) , inv .snd .snd .fst , inv .fst , tt )
  , λ τ₁ st₁ →
      let i₁ = invPop9 base (16 + sp) σ inv τ₁ st₁ in
      ( 16 + sp , i₁ .snd .snd .fst , i₁ .snd .fst , tt )
      , λ τ₂ st₂ →
          let i₂ = invPop10 base sp τ₁ i₁ τ₂ st₂ in
          i₂ .fst
          , λ τ₃ st₃ → pushSafe base sp τ₃ ge (invAddR base sp τ₂ i₂ τ₃ st₃)

addSeqWp : (base sp : Word) (σ : PSt) → Inv base (16 + (16 + sp)) σ
         → wp (sem addSeq) (Inv base (16 + sp)) σ
addSeqWp base sp σ inv σ' (τ₁ , st₁ , τ₂ , st₂ , τ₃ , st₃ , τ₄ , st₄ , Eq.refl) =
  invPush base sp τ₃ (invAddR base sp τ₂ i₂ τ₃ st₃) τ₄ st₄
  where
  i₁ = invPop9 base (16 + sp) σ inv τ₁ st₁
  i₂ = invPop10 base sp τ₁ i₁ τ₂ st₂

-- ------------------------------------------------------------------
-- ... AND THE INDUCTION.  Three cases, and the only thing that happens
-- in each is bookkeeping of OWNERSHIP; no address is ever compared with
-- another, which is precisely the difference from the hand proof.
-- ------------------------------------------------------------------

wp-++ : (p q : Program) (R : Gr) (σ : PSt)
      → wp (sem p) (wp (sem q) R) σ → wp (sem (p ++ q)) R σ
wp-++ p q R σ w σ' r =
  w (sem-++ p q σ σ' r .fst) (sem-++ p q σ σ' r .snd .fst)
    σ' (sem-++ p q σ σ' r .snd .snd)

compileInv : ∀ {u} (e : Exp u) (base sp : Word) (σ : PSt) → Ge sp base
           → Inv base sp σ
           → SafeP (compile e) σ × wp (sem (compile e)) (Inv base (16 + sp)) σ
compileInv (evar so) base sp σ ge inv =
  ( inv .fst , (λ τ st → pushSafe base sp τ ge (invLdrO _ base sp σ inv τ st)) )
  , λ σ' (τ , st , r) → pushWp base sp τ (invLdrO _ base sp σ inv τ st) σ' r
compileInv (elit _ n) base sp σ ge inv =
  ( inv .fst , (λ τ st → pushSafe base sp τ ge (invMovI n base sp σ inv τ st)) )
  , λ σ' (τ , st , r) → pushWp base sp τ (invMovI n base sp σ inv τ st) σ' r
compileInv (eadd usp ea eb) base sp σ ge inv =
  SafeP-++ (compile ea) (compile eb ++ addSeq) σ (A .fst)
    (λ τ r → SafeP-++ (compile eb) addSeq τ (B τ r .fst)
               (λ υ r' → addSeqSafe base sp υ ge (B τ r .snd υ r')))
  , wp-++ (compile ea) (compile eb ++ addSeq) (Inv base (16 + sp)) σ
      (λ τ r → wp-++ (compile eb) addSeq (Inv base (16 + sp)) τ
                 (λ υ r' → addSeqWp base sp υ (B τ r .snd υ r')))
  where
  ge' : Ge (16 + sp) base
  ge' = ge-addL 16 sp base ge

  A = compileInv ea base sp σ ge inv

  B : (τ : PSt) → sem (compile ea) σ τ
    → SafeP (compile eb) τ × wp (sem (compile eb)) (Inv base (16 + (16 + sp))) τ
  B τ r = compileInv eb base (16 + sp) τ ge' (A .snd τ r)

-- the incoming total state satisfies the invariant at its own stack
-- pointer: registers are outside the low region by construction, and
-- memory at or above `b` is not in it either
invHi : (s : St) → Inv (rg s x20) (rg s x20) (hi (rg s x20) s)
invHi s =
  tt , tt , Eq.refl
  , λ a g → Eq.transport (λ z → IsJ (maskM (ifM z (mm s a) nothing) (just (mm s a))))
                         (Eq.sym (ge-ltB a (rg s x20) g)) tt

-- THE OBLIGATION, DISCHARGED.
compileSafe : ∀ {u} (e : Exp u) (s : St) → SafeP (compile e) (hi (rg s x20) s)
compileSafe e s =
  compileInv e (rg s x20) (rg s x20) (hi (rg s x20) s)
             (ge-refl (rg s x20)) (invHi s) .fst

-- `pLow`, DERIVED.  Compare `AArch64Codegen.Post.pLow`.
compileLow : ∀ {u} (e : Exp u) (s : St)
           → (a : Word) → Lt a (rg s x20)
           → mm (exec (compile e) s) a Eq.≡ mm s a
compileLow e s = frameLow (compile e) (compileOK e) (rg s x20) s (compileSafe e s)

-- ... and it really is `Post.pLow` and not a lookalike: this typechecks
-- ONLY because the two statements are the same type, definitionally.
pLow-same : ∀ {u} (e : Exp u) (s : St) → Post e s (exec (compile e) s)
          → (a : Word) → Lt a (rg s x20)
          → mm (exec (compile e) s) a Eq.≡ mm s a
pLow-same e s P = P .pLow
