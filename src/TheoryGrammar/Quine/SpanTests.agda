{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SPAN QUINES, RUN.

  ONE ambient text, thirty-four characters, and every claim below is a
  `refl`: the span CYK filling its chart at typecheck time and the
  interpreter running on the parse tree it produced.  Nothing is
  postulated and nothing is assumed to terminate -- if a parse did not
  evaluate, the file would not compile.

      idx  0  1  2  3  4  5  6  7  8   9 10  11 12 13 14  15 16 17 18
           0  #  0  0  #  0  0  0  0   1  1   0  #  0  0   1  #  1  1

      idx 19  20 21 22 23  24 25 26 27 28 29 30 31 32 33
           0   1  #  1  1   0  1  0  #  0  0  1  1  0  0

  Six regions of it are programs and five of those are QUINES:

      ( 0 ,  4)   0#00          even offset   QUINE
      ( 2 ,  7)   00#0000       even offset   QUINE   -- overlaps (0,4)
      (11 ,  4)   0#00          ODD  offset   prints 1#11
      (15 ,  4)   1#11          ODD  offset   QUINE
      (20 ,  4)   1#11          even offset   prints 0#00
      (24 , 10)   010#001100    even offset   QUINE
      (26 ,  4)   0#00          even offset   QUINE   -- inside (24,10)
      (25 ,  7)   10#0011       ODD  offset   prints 11#1111

  and the whole thing derives from nothing at all.
-}
module TheoryGrammar.Quine.SpanTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Span

-- ==================================================================
-- §0  THE AMBIENT TEXT.  Written ONCE, as a list; `charAt` is the
--     lookup, and it is the only thing the grammar ever sees of the
--     text (`Spans.CYK`: the word enters only through `unitR`).
--     Everything past the end is `#`, which no program can cross.
-- ==================================================================

word : String
word = c0 ∷ c# ∷ c0 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ c0 ∷ c0            --  0 ..  8
     ∷ c1 ∷ c1                                                --  9 .. 10
     ∷ c0 ∷ c# ∷ c0 ∷ c0                                      -- 11 .. 14
     ∷ c1 ∷ c# ∷ c1 ∷ c1                                      -- 15 .. 18
     ∷ c0                                                     -- 19
     ∷ c1 ∷ c# ∷ c1 ∷ c1                                      -- 20 .. 23
     ∷ c0 ∷ c1 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ c0 ∷ c0        -- 24 .. 33
     ∷ c0 ∷ c1 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1                       -- 34 .. 40
     ∷ c1 ∷ c1 ∷ c# ∷ c1 ∷ c1 ∷ c1 ∷ c1                       -- 41 .. 47
     ∷ c0 ∷ c1 ∷ c1 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ c1 ∷ c1 ∷ c0 ∷ c0
                                                              -- 48 .. 60
     ∷ c0 ∷ c1 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1                       -- 61 .. 67
     ∷ []

lookupC : ℕ → String → Chr
lookupC _       []       = c#
lookupC zero    (c ∷ _)  = c
lookupC (suc n) (_ ∷ cs) = lookupC n cs

charAt : ℕ → Chr
charAt n = lookupC n word

open Text charAt public

-- the four texts that occur, named once
t0 t1 t00 t010 t10 : String
t0   = c0 ∷ c# ∷ c0 ∷ c0 ∷ []                                    -- 0#00
t1   = c1 ∷ c# ∷ c1 ∷ c1 ∷ []                                    -- 1#11
t00  = c0 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ c0 ∷ c0 ∷ []                     -- 00#0000
t010 = c0 ∷ c1 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ c0 ∷ c0 ∷ []      -- 010#001100
t10  = c1 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ []                     -- 10#0011

-- ==================================================================
-- §1  WHAT IS WRITTEN WHERE.  The three copies of `0#00` and the two
--     of `1#11` really are THE SAME CHARACTERS at different offsets --
--     which is what makes §4 a statement about position and not about
--     text.
-- ==================================================================

_ : passes (textOf at
             ( (0 , 4) ↦ t0 ∷ (11 , 4) ↦ t0 ∷ (26 , 4) ↦ t0
             ∷ (15 , 4) ↦ t1 ∷ (20 , 4) ↦ t1
             ∷ (2 , 7) ↦ t00 ∷ (24 , 10) ↦ t010 ∷ (25 , 7) ↦ t10
             ∷ [] ))
_ = refl

-- ==================================================================
-- §2  WHICH REGIONS ARE PROGRAMS.  A negative answer here is a
--     REFUTATION (the error grammar is `¬G _`), so the `false`s are
--     theorems that no parse tree exists -- not reports that none was
--     found.  See `no-whole` in §6.
-- ==================================================================

_ : passes (run (derives! ntS) at
             ( (0 ,  4) ↦ true    -- 0#00
             ∷ (2 ,  7) ↦ true    -- 00#0000
             ∷ (11 , 4) ↦ true    -- 0#00
             ∷ (15 , 4) ↦ true    -- 1#11
             ∷ (20 , 4) ↦ true    -- 1#11
             ∷ (25 , 7) ↦ true    -- 10#0011
             ∷ (26 , 4) ↦ true    -- 0#00
             ∷ [] ))
_ = refl

-- THE FRAGMENT IS NOT THE TEXT.  `(0,9)` is `0#00#0000`, which properly
-- contains two quines and is not a program itself: two hashes, and the
-- grammar allows one.  This is the span theory's sentence, and the
-- string theory has no way to say it -- there, the program IS the input.
_ : passes (run (derives! ntS) at
             ( (0 , 9) ↦ false    -- 0#00#0000 : two hashes
             ∷ (0 , 3) ↦ false    -- 0#0       : odd data
             ∷ (1 , 4) ↦ false    -- #00#      : no code
             ∷ (2 , 4) ↦ false    -- 00#0      : odd data
             ∷ (9 , 4) ↦ false    -- 110#      : no data
             ∷ [] ))
_ = refl

-- ==================================================================
-- §3  ... AND WHAT THEY PRINT.  For a quine the expected value is
--     `textOf s` -- the region's OWN text -- so each of these lines
--     says "this region prints itself" with the region written once.
-- ==================================================================

_ : passes (runOut ntS at
             ( (0 ,  4) ↦ just (textOf (0 ,  4))
             ∷ (2 ,  7) ↦ just (textOf (2 ,  7))
             ∷ (15 , 4) ↦ just (textOf (15 , 4))
             ∷ (24 , 10) ↦ just (textOf (24 , 10))
             ∷ (26 , 4) ↦ just (textOf (26 , 4))
             ∷ [] ))
_ = refl

-- ==================================================================
-- §4  THE POINT OF THE FILE: POSITION-DEPENDENT SELF-REFERENCE.
--
-- `(0,4)`, `(11,4)` and `(26,4)` are THE SAME FOUR CHARACTERS (§1).
-- Two of them are quines and one is not, and the difference is nothing
-- but the offset.  Likewise `(15,4)` and `(20,4)`.
--
-- And a displaced quine does not become nonsense -- it becomes ITS
-- SIBLING.  `0#00` moved to an odd offset prints `1#11`; `1#11` moved
-- to an even one prints `0#00`.  The two four-character quines are a
-- 2-cycle under relocation, and each is the other's output at the
-- wrong address.
-- ==================================================================

_ : passes (runOut ntS at
             ( (11 , 4) ↦ just t1     -- 0#00 at an ODD offset prints 1#11
             ∷ (20 , 4) ↦ just t0     -- 1#11 at an EVEN offset prints 0#00
             ∷ [] ))
_ = refl

-- ... and a program whose data is not the quoted form of its code
-- prints some OTHER program, at its own address.  `10#0011` at offset
-- 25 has data decoding to `01`, which the odd address patches to `11`.
_ : passes (runOut ntS at
             ( (25 , 7) ↦ just (c1 ∷ c1 ∷ c# ∷ c1 ∷ c1 ∷ c1 ∷ c1 ∷ []) ∷ [] ))
_ = refl

-- ==================================================================
-- §5  THE QUINE EQUATION, in the calculus.
--
-- `IsQuineAt s pf` is
--
--     (interp S ∘g selfLit s pf) s (⌈⌉-pt s)  ≡  (textOf s , tt)
--
-- -- the region's parse tree, PINNED to the region by `⌈_⌉` and
-- EXTRACTED from the decision by `witness`, run through the
-- interpreter, is the region's own text.  The `refl` on the left of
-- each line is the decision procedure; the `refl` on the right is the
-- fixed point.
-- ==================================================================

quine-0-4 : IsQuineAt (0 , 4) refl              -- 0#00        at 0
quine-0-4 = refl

quine-15-4 : IsQuineAt (15 , 4) refl            -- 1#11        at 15
quine-15-4 = refl

quine-2-7 : IsQuineAt (2 , 7) refl              -- 00#0000     at 2
quine-2-7 = refl

quine-24-10 : IsQuineAt (24 , 10) refl          -- 010#001100  at 24
quine-24-10 = refl

quine-26-4 : IsQuineAt (26 , 4) refl            -- 0#00        at 26
quine-26-4 = refl

-- ==================================================================
-- §6  OVERLAP AND NESTING -- both questions, answered by the same text.
--
-- A quine `C # enc C` has ONE hash, so a sub-quine sharing that hash is
-- a PREFIX-region of it; a sub-quine with its own hash must lie to the
-- right of it.  Both cases occur here.
--
--   NESTED.  `(26,4)` is inside `(24,10)`, and both are quines.  This
--   is the general fact that `C # enc C` at `p` contains a quine at
--   `p + j` exactly when `C` has an EVEN period `j` with `0 < j < |C|`
--   -- even, because the sub-code begins with `C j = C 0` and must
--   agree with the parity of `p + j`.  `C = 010`, `j = 2` is the
--   smallest instance, and it is `(24,10) ⊃ (26,4)`.
--
--   OVERLAPPING, NEITHER INSIDE THE OTHER.  `(0,4) = [0,4)` and
--   `(2,7) = [2,9)` share the two characters at 2 and 3.  They use
--   DIFFERENT hashes -- position 1 and position 4 -- which is exactly
--   what the previous paragraph says is required.
--
-- Both facts are already `refl`-checked in §3 and §5; this section only
-- names them, and adds the containing region's refutation.
-- ==================================================================

-- the two overlapping quines, as parse trees.  `witness` reads them out
-- of the same decision procedure that answered §2.
tree-0-4 : Deriv ntS (0 , 4)
tree-0-4 = selfDeriv (0 , 4) refl

tree-2-7 : Deriv ntS (2 , 7)
tree-2-7 = selfDeriv (2 , 7) refl

-- ... and the region containing BOTH of them is not a program.  A
-- theorem, not a report: `noDeriv` turns the `false` of §2 into the
-- content of the error branch, which at `E = ¬G _` is a refutation.
no-whole : Deriv ntS (0 , 9) → E.⊥* {ℓ-zero}
no-whole = noDeriv (0 , 9) refl

-- ... and so are the other four `false`s of §2, each from the `refl`
-- that batch already proved.  §2's comment claims they are theorems;
-- these are the theorems.
no-odd-data : Deriv ntS (0 , 3) → E.⊥* {ℓ-zero}      -- 0#0  : odd datum
no-odd-data = noDeriv (0 , 3) refl

no-code : Deriv ntS (1 , 4) → E.⊥* {ℓ-zero}          -- #00# : no code
no-code = noDeriv (1 , 4) refl

no-odd-data' : Deriv ntS (2 , 4) → E.⊥* {ℓ-zero}     -- 00#0 : odd datum
no-odd-data' = noDeriv (2 , 4) refl

no-data : Deriv ntS (9 , 4) → E.⊥* {ℓ-zero}          -- 110# : no datum
no-data = noDeriv (9 , 4) refl

-- the nested pair, likewise
tree-24-10 : Deriv ntS (24 , 10)
tree-24-10 = selfDeriv (24 , 10) refl

tree-26-4 : Deriv ntS (26 , 4)
tree-26-4 = selfDeriv (26 , 4) refl

-- ==================================================================
-- §7  THE FAMILY, AND THE SCALE.
--
-- The quines are `a ++ "#" ++ enc a` for any nonempty bit string `a`,
-- placed at an offset whose parity is `a`'s first letter.  Four of them
-- live in the tail of the text, at four sizes and both parities:
--
--     (34 ,  7)   01#0011           a = 01     even offset
--     (41 ,  7)   11#1111           a = 11     ODD  offset
--     (48 , 13)   0110#00111100     a = 0110   even offset
--
-- and one displaced copy,
--
--     (61 ,  7)   01#0011           a = 01     ODD  offset
--
-- which is NOT a quine and prints `11#1111` -- the member of the family
-- whose code is `01` with its first letter corrected to the address.
-- Together with §3 this is the same `refl` at 4, 7, 10 and 13
-- characters, each one a full run of the span chart and the
-- interpreter.
-- ==================================================================

fam01 fam11 fam0110 : String
fam01   = c0 ∷ c1 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ []
fam11   = c1 ∷ c1 ∷ c# ∷ c1 ∷ c1 ∷ c1 ∷ c1 ∷ []
fam0110 = c0 ∷ c1 ∷ c1 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ c1 ∷ c1 ∷ c0 ∷ c0 ∷ []

-- the same characters at 34 and at 61 -- one even, one odd
_ : passes (textOf at
             ( (34 , 7) ↦ fam01 ∷ (61 , 7) ↦ fam01
             ∷ (41 , 7) ↦ fam11 ∷ (48 , 13) ↦ fam0110 ∷ [] ))
_ = refl

-- three quines, at three sizes and both parities ...
_ : passes (runOut ntS at
             ( (34 ,  7) ↦ just (textOf (34 ,  7))
             ∷ (41 ,  7) ↦ just (textOf (41 ,  7))
             ∷ (48 , 13) ↦ just (textOf (48 , 13))
             ∷ [] ))
_ = refl

-- ... and the displaced copy, which prints its sibling
_ : passes (runOut ntS at ( (61 , 7) ↦ just fam11 ∷ [] ))
_ = refl

quine-34-7 : IsQuineAt (34 , 7) refl            -- 01#0011        at 34
quine-34-7 = refl

quine-41-7 : IsQuineAt (41 , 7) refl            -- 11#1111        at 41
quine-41-7 = refl

quine-48-13 : IsQuineAt (48 , 13) refl          -- 0110#00111100  at 48
quine-48-13 = refl
