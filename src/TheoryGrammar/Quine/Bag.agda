{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A QUINE IN THE BAG THEORY.

  `TheoryGrammar.Quine.Base` builds a quine over the free monoid: a
  four-character program `0#00`, whose data is the quoted code and whose
  `#` marks where the one ends and the other begins.  This file asks
  what survives when the theory is the free COMMUTATIVE monoid --
  `Instances.Bags`, where `⊗ˢ` splits a MULTISET and `⊗-comm` is a term.

  Three things change, and each of them is forced.

  ------------------------------------------------------------------
  (1)  THE `#` BECOMES A TAG, BECAUSE THERE IS NO POSITION.

  `Quine.Base`'s `R → H E` says the data comes AFTER the hash.  At bags
  there is no "after": a parse is a PARTITION, not a cut, and

      sepFree : (Deriv ntK ⊗' Deriv ntD) ⊢ (Deriv ntD ⊗' Deriv ntK)

  is `⊗-comm`, a term of this file.  There is deliberately no such term
  in `Quine.Base`.  So the split of a program into its code and its data
  cannot be marked by WHERE the separator sits; it has to be carried by
  the letters themselves.  Hence the alphabet

      k0 k1     CODE letters                q0 q1     DATA letters

  and the grammar's root rule `S → K D` -- "a code part and a data
  part", in either order, and the tags make the partition unique.  This
  is the crux: a self-delimiting alphabet replaces a positional marker.

  The trade is exact and worth naming.  In the free monoid QUOTING COSTS
  LENGTH -- `Quine.Base`'s `enc c = c c` doubles the text.  In the free
  commutative monoid quoting costs ALPHABET -- `q_` is `k_` tagged, and
  the text does not grow at all.  That is why the shortest bag quine is
  TWO elements against the string quine's four.

  ------------------------------------------------------------------
  (2)  THE INTERPRETER MUST BE A COMMUTATIVE ALGEBRA, AND THAT COLLAPSES
       "THE DATA" TO A PAIR OF NUMBERS.

  A bag of `n` elements has `2ⁿ` interleavings, so the grammar below is
  massively ambiguous: `K → Kb K` can pull the code letters off in any
  order.  The decision procedure returns SOME parse tree.  So the output
  is well defined only if the algebra does not depend on which -- i.e.
  only if the algebra is COMMUTATIVE (`algebra-comm`, below).

  `Quine.Base`'s decoder is not.  Its rule `E → B O` means `b ∷ d`, and
  cons is not commutative; that algebra simply cannot be transported.
  The free commutative monoid on the bits IS `ℕ × ℕ`, so the bag
  interpreter's "decoded data" is a pair of COUNTS, and there is no
  choice about this.  Everything else follows.

  ------------------------------------------------------------------
  (3)  ... SO THE QUINE EQUATION BECOMES ARITHMETIC.

  A source over this 4-letter alphabet is, as a bag, exactly its count
  vector `(a' , b' , a , b) ∈ ℕ⁴` -- `a'` code-zeros, `b'` code-ones,
  `a` data-zeros, `b` data-ones.  The program prints `emit b' (a , b)`,
  where the OPCODE `b'` is the only reading of the code a commutative
  theory admits (there is no "first bit"; a count is all there is).  So

      QuineEq a' b' a b   =   emit b' (a , b) ≡ (a' , b' , a , b)

  is THE quine equation, three equations in ℕ, and it is settled
  completely below:

      quine-0     : every  k0^a q0^a          is a quine   (opcode 0)
      quine-1     : every  k0^a k1 q0^a q1    is a quine   (opcode 1)
      no-quine-2+ : opcode ≥ 2 has no quines at all

  Compare `Quine.Base`, where opcode 0 has the quine family and opcode 1
  has NONE -- and where the reason opcode 1 has none is that its output
  begins with a doubled letter while its source begins with `1`.  That
  argument is about POSITION, and the bag theory has no term for it.
  Here the two opcodes are literally the same map

      opcode-irrelevant : (d : Cnt) → emit 0 d ≡ emit 1 d

  because `⊎M` is commutative -- which is the value-level shadow of
  `⊗-comm`.  Opcode 1 therefore ACQUIRES a quine family it did not have
  over strings.  What kills opcode 2 instead is arithmetic: it emits the
  quote twice, and `a + a ≡ a` forces `a ≡ 0`.

  ------------------------------------------------------------------
  IS THIS EASIER OR HARDER?  Easier, and the reason is a real loss.

  A string of length `n` over `Σ` carries `n log|Σ|` bits; a bag over
  `Σ` carries only `|Σ|` numbers, because the free commutative monoid on
  a finite alphabet IS `ℕ^Σ`.  So the source text a bag quine has to
  reproduce is exponentially less information than a string quine's, and
  "print your own source" degenerates from a diagonal argument to a
  fixed point of a map `ℕ⁴ → ℕ⁴`.  There is no pairing, hence no coding
  of descriptions, hence nothing for Kleene's recursion theorem to do.
  That is the honest finding: the bag quine is a genuine fixed point of
  a genuine interpreter, and it is short exactly because the theory
  cannot tell its own source texts apart very well.

  What it buys, and what the tests show, is that ONE bag quine is an
  equivalence class of texts at once: `k0 q0` and `q0 k0` are the same
  program, and the 4-element quine is 24 texts.  The interpreter prints
  the class's canonical representative from any member of it.

  ------------------------------------------------------------------
  THE GRAMMAR, in commutative Chomsky normal form.  Every binary rule
  is `⊗ˢ appop`, which at bags is a PARTITION with both parts nonempty.

      S  → K D                    the program: a code part, a data part
      K  → k0 | k1 | Kb K         a nonempty bag of code letters
      D  → q0 | q1 | Db D         a nonempty bag of data letters
      Kb → k0 | k1
      Db → q0 | q1

  The one-letter left slot is kept from `Quine.Base` for the same
  reason: `löb` does not tabulate, so a rule whose left slot can be
  large makes the search re-descend.  At bags this matters more, not
  less -- the cut space is `2ⁿ`, so a wrong partition must die at the
  literal matcher immediately, and the TAGS are what make it die.
-}
module TheoryGrammar.Quine.Bag where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable
open import TheoryGrammar.SemanticAction

-- ==================================================================
-- §0  THE ALPHABET.  Four letters, and every one of them says which
--     half of the program it belongs to.  That is the whole of what
--     replaces `Quine.Base`'s `#`.
-- ==================================================================

data Chr : Type₀ where
  k0 k1 q0 q1 : Chr

-- the two letter classes, as TYPES (one unit-rule schema, not two)
Code? : Chr → Type₀
Code? k0 = Unit
Code? k1 = Unit
Code? q0 = ⊥
Code? q1 = ⊥

Quo? : Chr → Type₀
Quo? k0 = ⊥
Quo? k1 = ⊥
Quo? q0 = Unit
Quo? q1 = Unit

open import TheoryGrammar.Quine.BagCYK Chr public

-- ==================================================================
-- §1  THE GRAMMAR
-- ==================================================================

data NT : Type₀ where ntS ntK ntD ntKb ntDb : NT

unitR : NT → Chr → Type₀
unitR ntS  c = ⊥
unitR ntK  c = Code? c
unitR ntD  c = Quo?  c
unitR ntKb c = Code? c
unitR ntDb c = Quo?  c

binR : NT → NT → NT → Type₀
binR ntS ntK  ntD = Unit     -- S → K D
binR ntK ntKb ntK = Unit     -- K → Kb K
binR ntD ntDb ntD = Unit     -- D → Db D
binR _   _    _   = ⊥

open Parser NT unitR binR public

allRules : (P : NT) → List (Rule P)
allRules ntS  = inr (ntK , ntD , tt) ∷ []
allRules ntK  = inl (k0 , tt) ∷ inl (k1 , tt) ∷ inr (ntKb , ntK , tt) ∷ []
allRules ntD  = inl (q0 , tt) ∷ inl (q1 , tt) ∷ inr (ntDb , ntD , tt) ∷ []
allRules ntKb = inl (k0 , tt) ∷ inl (k1 , tt) ∷ []
allRules ntDb = inl (q0 , tt) ∷ inl (q1 , tt) ∷ []

-- Completeness.  Mechanical: for each nonterminal, every pair that is
-- NOT a right-hand side reduces to `⊥`.
allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete ntS (inl (_ , ()))
allComplete ntS (inr (ntS  , _ , ()))
allComplete ntS (inr (ntKb , _ , ()))
allComplete ntS (inr (ntD  , _ , ()))
allComplete ntS (inr (ntDb , _ , ()))
allComplete ntS (inr (ntK , ntS  , ()))
allComplete ntS (inr (ntK , ntK  , ()))
allComplete ntS (inr (ntK , ntKb , ()))
allComplete ntS (inr (ntK , ntD  , tt)) = here
allComplete ntS (inr (ntK , ntDb , ()))
allComplete ntK (inl (k0 , tt)) = here
allComplete ntK (inl (k1 , tt)) = there here
allComplete ntK (inl (q0 , ()))
allComplete ntK (inl (q1 , ()))
allComplete ntK (inr (ntS  , _ , ()))
allComplete ntK (inr (ntK  , _ , ()))
allComplete ntK (inr (ntD  , _ , ()))
allComplete ntK (inr (ntDb , _ , ()))
allComplete ntK (inr (ntKb , ntS  , ()))
allComplete ntK (inr (ntKb , ntK  , tt)) = there (there here)
allComplete ntK (inr (ntKb , ntKb , ()))
allComplete ntK (inr (ntKb , ntD  , ()))
allComplete ntK (inr (ntKb , ntDb , ()))
allComplete ntD (inl (q0 , tt)) = here
allComplete ntD (inl (q1 , tt)) = there here
allComplete ntD (inl (k0 , ()))
allComplete ntD (inl (k1 , ()))
allComplete ntD (inr (ntS  , _ , ()))
allComplete ntD (inr (ntK  , _ , ()))
allComplete ntD (inr (ntD  , _ , ()))
allComplete ntD (inr (ntKb , _ , ()))
allComplete ntD (inr (ntDb , ntS  , ()))
allComplete ntD (inr (ntDb , ntK  , ()))
allComplete ntD (inr (ntDb , ntKb , ()))
allComplete ntD (inr (ntDb , ntD  , tt)) = there (there here)
allComplete ntD (inr (ntDb , ntDb , ()))
allComplete ntKb (inl (k0 , tt)) = here
allComplete ntKb (inl (k1 , tt)) = there here
allComplete ntKb (inl (q0 , ()))
allComplete ntKb (inl (q1 , ()))
allComplete ntKb (inr (_ , _ , ()))
allComplete ntDb (inl (q0 , tt)) = here
allComplete ntDb (inl (q1 , tt)) = there here
allComplete ntDb (inl (k0 , ()))
allComplete ntDb (inl (k1 , ()))
allComplete ntDb (inr (_ , _ , ()))

-- ==================================================================
-- §2  THE ONE EXTERNAL INPUT: decidability of the alphabet.  Exactly
--     `Quine.Base`'s.  It enters the calculus once, as `litProbe`.
-- ==================================================================

decEqC : (a b : Chr) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqC k0 k0 = inl Eq.refl
decEqC k1 k1 = inl Eq.refl
decEqC q0 q0 = inl Eq.refl
decEqC q1 q1 = inl Eq.refl
decEqC k0 k1 = inr λ ()
decEqC k0 q0 = inr λ ()
decEqC k0 q1 = inr λ ()
decEqC k1 k0 = inr λ ()
decEqC k1 q0 = inr λ ()
decEqC k1 q1 = inr λ ()
decEqC q0 k0 = inr λ ()
decEqC q0 k1 = inr λ ()
decEqC q0 q1 = inr λ ()
decEqC q1 k0 = inr λ ()
decEqC q1 k1 = inr λ ()
decEqC q1 q0 = inr λ ()

decEqB : (u v : Bag) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
decEqB []      []      = inl Eq.refl
decEqB []      (_ ∷ _) = inr λ ()
decEqB (_ ∷ _) []      = inr λ ()
decEqB (a ∷ u) (b ∷ v) = both (decEqC a b) (decEqB u v)
  where both : (a Eq.≡ b) ⊎ No (a Eq.≡ b) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
             → ((a ∷ u) Eq.≡ (b ∷ v)) ⊎ No ((a ∷ u) Eq.≡ (b ∷ v))
        both (inl Eq.refl) (inl Eq.refl) = inl Eq.refl
        both (inr k)       _             = inr λ { Eq.refl → k Eq.refl }
        both _             (inr k)       = inr λ { Eq.refl → k Eq.refl }

litProbe : (c : Chr) → Probe ⌈ c ∷ [] ⌉
litProbe c w _ = decEqB w (c ∷ [])

open Decide allRules allComplete litProbe public

-- ==================================================================
-- §3  THE SEPARATOR IS FREE, AS A TERM.
--
-- `Quine.Base` marks the boundary between code and data by WHERE the
-- `#` sits; there is nothing in that theory saying the two halves may
-- be exchanged.  Here that statement is `⊗-comm`, and it costs one
-- line -- which is the same fact `Instances.Bags.JSON` records for key
-- order.  Everything about the encoding below is downstream of it.
-- ==================================================================

sepFree : (Deriv ntK ⊗' Deriv ntD) ⊢ (Deriv ntD ⊗' Deriv ntK)
sepFree = ⊗-comm

-- ==================================================================
-- §4  THE VALUES.  The free commutative monoid on the bits (`Cnt`) and
--     on the alphabet (`Multi`).  These are the only value types a
--     commutative theory allows -- see the header, (2).
-- ==================================================================

Cnt : Type₀
Cnt = ℕ × ℕ                      -- (# of 0-bits , # of 1-bits)

addC : Cnt → Cnt → Cnt
addC (a , b) (c , d) = (a + c) , (b + d)

-- THE OBLIGATION `⊗-comm` IMPOSES.  A parse of a bag is a partition and
-- the grammar is ambiguous, so the interpreter's answer is well defined
-- only because this holds.  `Quine.Base`'s decoder (`E → B O ↦ b ∷ d`)
-- fails it, which is exactly why it cannot be ported.
algebra-comm : (x y : Cnt) → addC x y ≡ addC y x
algebra-comm (a , b) (c , d) i = (+-comm a c i) , (+-comm b d i)

-- a bag over the alphabet, as its count vector: (k0 , k1 , q0 , q1)
Multi : Type₀
Multi = ℕ × ℕ × ℕ × ℕ

_⊎M_ : Multi → Multi → Multi
(a , b , c , d) ⊎M (a' , b' , c' , d') = (a + a') , (b + b') , (c + c') , (d + d')

infixr 5 _⊎M_

-- `Multi` is the free COMMUTATIVE monoid on the alphabet, and these two
-- are why.  `⊎M-comm` is what `opcode-irrelevant` (§5) rests on, and
-- `⊎M-assoc`/`⊎M-swap` are what makes the printer's reading of an
-- interleaving independent of the order it happens to unpick it in
-- (`Quine.BagRoundTrip`).
⊎M-comm : (m n : Multi) → m ⊎M n ≡ n ⊎M m
⊎M-comm (a , b , c , d) (a' , b' , c' , d') i =
  +-comm a a' i , +-comm b b' i , +-comm c c' i , +-comm d d' i

⊎M-assoc : (m n p : Multi) → m ⊎M (n ⊎M p) ≡ (m ⊎M n) ⊎M p
⊎M-assoc (a , b , c , d) (a' , b' , c' , d') (a'' , b'' , c'' , d'') i =
  +-assoc a a' a'' i , +-assoc b b' b'' i ,
  +-assoc c c' c'' i , +-assoc d d' d'' i

⊎M-swap : (m n p : Multi) → m ⊎M (n ⊎M p) ≡ n ⊎M (m ⊎M p)
⊎M-swap m n p =
  ⊎M-assoc m n p ∙ cong (_⊎M p) (⊎M-comm m n) ∙ sym (⊎M-assoc n m p)

-- what one letter contributes
bitM : Chr → Multi
bitM k0 = 1 , 0 , 0 , 0
bitM k1 = 0 , 1 , 0 , 0
bitM q0 = 0 , 0 , 1 , 0
bitM q1 = 0 , 0 , 0 , 1

-- the CANONICAL SURJECTION from texts to programs.  `Bag` is `List Chr`
-- and the carrier really does remember the order; `count` is the
-- quotient by the theory's own inability to see it.
count : Bag → Multi
count []      = 0 , 0 , 0 , 0
count (x ∷ w) = bitM x ⊎M count w

-- ... and a SECTION of it: the class's canonical representative.  This
-- is a choice, and it is the only one made anywhere below; it exists so
-- that a test can be written `src ↦ just src` with readable literals.
rep : ℕ → Chr → Bag
rep zero    c = []
rep (suc n) c = c ∷ rep n c

canon : Multi → Bag
canon (a , b , c , d) = rep a k0 ++ rep b k1 ++ rep c q0 ++ rep d q1

-- ==================================================================
-- §5  QUOTING, AND THE INSTRUCTION SET.
--
-- `Quine.Base`'s `enc c = c c` doubles the text.  Here quoting is
-- RETAGGING: `codeM d` prints the bits `d` as CODE letters, `quoteM d`
-- prints them as DATA letters, and neither changes the size.  That one
-- substitution is what makes the bag quine half the length.
-- ==================================================================

codeM : Cnt → Multi
codeM (a , b) = a , b , 0 , 0

quoteM : Cnt → Multi
quoteM (a , b) = 0 , 0 , a , b

-- THE OPCODE.  A commutative theory has no "first bit of the code";
-- the only reading of a code part is its COUNT, so the opcode is the
-- number of 1-bits in the code, and there are as many instructions as
-- there are numbers.  Three suffice:
--
--     0     print the data as code, then quote it
--     1     quote the data, then print it as code   -- the SAME map
--     2+    print it as code and quote it TWICE
emit : ℕ → Cnt → Multi
emit zero             d = codeM  d ⊎M quoteM d
emit (suc zero)       d = quoteM d ⊎M codeM  d
emit (suc (suc _))    d = codeM  d ⊎M quoteM d ⊎M quoteM d

-- THE PUNCHLINE, AS A THEOREM.  `Quine.Base`'s two opcodes are the two
-- ORDERS of the same two pieces, and over strings they are different
-- programs -- one has a quine family and the other has none.  Over bags
-- they are one program.  This is `⊗-comm` at the level of values.
opcode-irrelevant : (d : Cnt) → emit 0 d ≡ emit 1 d
opcode-irrelevant (a , b) i =
  (+-zero a i) , (+-zero b i) , (sym (+-zero a) i) , (sym (+-zero b) i)

-- ==================================================================
-- §6  THE QUINE EQUATION, SOLVED.
--
-- A source with code counts `(a' , b')` and data counts `(a , b)` IS
-- the bag `(a' , b' , a , b)`, and it prints `emit b' (a , b)`.  So
-- being a quine is this, and nothing else.
-- ==================================================================

QuineEq : ℕ → ℕ → ℕ → ℕ → Type₀
QuineEq a' b' a b = emit b' (a , b) ≡ (a' , b' , a , b)

-- OPCODE 0: the family `k0^a q0^a`, shortest member `k0 q0` -- TWO
-- elements, against `Quine.Base`'s four-character `0#00`.
quine-0 : (a : ℕ) → QuineEq a 0 a 0
quine-0 a i = (+-zero a i) , 0 , a , 0

-- OPCODE 1: the family `k0^a k1 q0^a q1`, shortest member `k1 q1`.
-- Over strings this opcode has NO quines at all; here it has as many
-- as opcode 0, by `opcode-irrelevant`.
quine-1 : (a : ℕ) → QuineEq a 1 a 1
quine-1 a i = a , 1 , (+-zero a i) , 1

-- OPCODE ≥ 2: none.  And the argument is ARITHMETIC -- `a + a ≡ a`
-- forces `a ≡ 0` -- where the string theory's argument at its dead
-- opcode was positional ("the output starts with a doubled letter").
-- That substitution is the whole difference between the two theories.
no-quine-2+ : (n a' a b : ℕ) → QuineEq a' (suc (suc n)) a b → ⊥
no-quine-2+ n a' a b p = znots (sym b≡0 ∙ sym (+-zero b) ∙ opc)
  where
    opc : b + 0 ≡ suc (suc n)
    opc = cong (λ z → fst (snd z)) p

    dbl : b + b ≡ b
    dbl = cong (λ z → snd (snd (snd z))) p

    b≡0 : b ≡ 0
    b≡0 = inj-m+ (dbl ∙ sym (+-zero b))

-- ==================================================================
-- §7  THE INTERPRETER, as a semantic action.  One meaning per
--     nonterminal, one metalanguage combination per production.
--
--         Kb , Db  ↦ one letter's bit-count
--         K        ↦ the code's bit-counts       (the opcode lives here)
--         D        ↦ the DECODED data's bit-counts
--         S        ↦ THE OUTPUT
--
--     Every combination is `addC`, which is commutative -- which is
--     what makes the answer independent of the parse tree the ambiguous
--     grammar happens to hand back.
-- ==================================================================

module AI = ActInd bagFib ℓ-zero NT (λ _ → tt)

-- what a code letter and a data letter contribute
bitOf : Chr → Cnt
bitOf k0 = 1 , 0
bitOf k1 = 0 , 1
bitOf q0 = 1 , 0
bitOf q1 = 0 , 1

module Interp (X : Type₀) (x₀ : X) (root : Cnt → Cnt → X) where

  Val : NT → Type₀
  Val ntS  = X                      -- THE OUTPUT
  Val ntK  = Cnt
  Val ntD  = Cnt
  Val ntKb = Cnt
  Val ntDb = Cnt

  unitVal : (P : NT) (c : Chr) → unitR P c → Val P
  unitVal ntS  c ()
  unitVal ntK  c pf = bitOf c
  unitVal ntD  c pf = bitOf c
  unitVal ntKb c pf = bitOf c
  unitVal ntDb c pf = bitOf c

  binVal : (P Q T : NT) → binR P Q T → Val Q → Val T → Val P
  binVal ntS ntK  ntD tt c d = root c d       -- S → K D : run the opcode
  binVal ntK ntKb ntK tt x y = addC x y       -- K → Kb K
  binVal ntD ntDb ntD tt x y = addC x y       -- D → Db D
  binVal ntS _ _ _ _ _ = x₀                   -- (unreachable)
  binVal ntK _ _ _ _ _ = 0 , 0
  binVal ntD _ _ _ _ _ = 0 , 0
  binVal ntKb _ _ _ _ _ = 0 , 0
  binVal ntDb _ _ _ _ _ = 0 , 0

  Mot : G.Ix → Type₀
  Mot i = Δ (Val (i .fst)) (i .snd)

  alg : AI.ActAlg CYKF Val
  alg P = ⊕ᴰ-E branch
    where
      slotX : NT → NT → Bool → Type₀
      slotX Q T true  = Val Q
      slotX Q T false = Val T

      branch : (r : Rule P) → G.⟦ ruleF P r ⟧c Mot ⊢ Δ (Val P)
      branch (inl (c , pf))     = pureA (Val P) (unitVal P c pf)
      branch (inr (Q , T , pf)) =
        mapA (λ f → binVal P Q T pf (f true) (f false))
             (⊗A appop {A = λ a → G.⟦ binSlot Q T a ⟧c Mot} (slotX Q T)
                 (λ { true  → &ᴰA Bool true idA
                    ; false → &ᴰA Bool true idA }))

  interp : (P : NT) → Deriv P ⊢ Δ (Val P)
  interp = AI.recA alg

  -- THE PIPELINE, still a term
  outD : (P : NT) → ⊤G ⊢ Result (¬G Deriv P) (Δ (Val P))
  outD P = mapR (¬G Deriv P) (Δ (Val P)) (interp P) ∘g derives? P

  -- the only externalisation, and it belongs in a `refl` line
  runOut : (P : NT) → Bag → Maybe (Val P)
  runOut P = runΔ (Val P) (¬G Deriv P) (outD P)

derives! : (P : NT) → ⊤G ⊢ Δ Bool
derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

-- THE QUINE INTERPRETER: the root prints, and the opcode is the code's
-- 1-count -- the only reading a commutative theory offers.
root : Cnt → Cnt → Multi
root (a' , b') d = emit b' d

open Interp Multi (0 , 0 , 0 , 0) root public

-- ==================================================================
-- §8  READING THE OUTPUT BACK AS A TEXT.
--
-- `interp ntS` produces the output MULTISET, which is the honest
-- answer.  `canon` picks the class's canonical text so that a test can
-- be written with literals; it is applied by `mapA`, so the pipeline
-- never leaves the calculus.
-- ==================================================================

outBagD : ⊤G ⊢ Result (¬G Deriv ntS) (Δ Bag)
outBagD = mapR (¬G Deriv ntS) (Δ Bag) (mapA canon (interp ntS)) ∘g derives? ntS

runOutBag : Bag → Maybe Bag
runOutBag = runΔ Bag (¬G Deriv ntS) outBagD
