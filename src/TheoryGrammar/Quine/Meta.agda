{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE META-CIRCULAR QUINE:  a text that parses itself AND says what
  grammar it was parsed by.

  `Quine.Tiny`'s `0#00` prints itself, but its data is arbitrary -- any
  bit string would have done, and the fixpoint is only about the text.
  Here the data is not arbitrary: the code half of the program is an
  ENCODING OF THE GRAMMAR'S OWN RULE TABLE, so

      metaSrc  =  ⌜G⌝  #  quote ⌜G⌝           where G is THIS grammar

  and the single `refl` at the end of the file asserts three things at
  once, by running the decision procedure on `metaSrc`:

      (1) `metaSrc` DERIVES from `S` -- it is a program of `G`;
      (2) its output is `metaSrc` -- it is a quine;
      (3) the table it decodes to is `theTable` -- and `theTable` is
          `allRules` reified, the very table the decision procedure is
          driven by (`inTable`, below, is `allComplete` -- the
          completeness hypothesis `Decide` demands -- transported along
          the reification).

  So the loop closes: the text is in the language of the grammar it
  describes, and describes the grammar that accepts it.

  ------------------------------------------------------------------
  WHAT IS AND IS NOT ACHIEVED.

  ACHIEVED.  The self-description is checked against the parser's own
  rule table -- not against a copy of it -- and the check is by
  evaluation, at the literal text, with `⌈_⌉` pinning the text (see
  `metaLit`).  Nothing is postulated.

  NOT ACHIEVED.  The decoder `decTable` is a metalanguage function on
  the decoded bit string, not a second GRAMMAR: `G` parses `metaSrc` as
  "bits, a hash, and pairs", and the production structure of the
  description is then read off by `decProd`.  The fully meta-circular
  statement would have `G` itself be a grammar OF GRAMMAR DESCRIPTIONS,
  so that the parse tree of `metaSrc` already IS the rule table and
  `decTable` disappears.  That is a strictly bigger grammar, and its own
  description is correspondingly longer; see the note at the foot of
  this file for the measured obstruction.
-}
module TheoryGrammar.Quine.Meta where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe; just; nothing)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Base

-- ==================================================================
-- §1  THE GRAMMAR, REIFIED.
--
-- `Rule P` is the description's own notion of production, and
-- `allRules`/`allComplete` are the finite table the decision procedure
-- consumes.  `reify` forgets the proofs; `inTable` says nothing was
-- lost, and its proof is `allComplete` and nothing else.
-- ==================================================================

data Prod : Type₀ where
  unitP : NT → Chr → Prod
  binP  : NT → NT → NT → Prod

Table : Type₀
Table = List Prod

reify : (P : NT) → Rule P → Prod
reify P (inl (c , _))     = unitP P c
reify P (inr (Q , T , _)) = binP P Q T

rulesOf : NT → Table
rulesOf P = map (reify P) (allRules P)

-- EVERY production of the grammar is in the table.  One line, and the
-- input is the parser's own completeness proof.
inTable : (P : NT) (r : Rule P) → reify P r ∈L rulesOf P
inTable P r = ∈map (reify P) (allComplete P r)

-- the whole table.  The order puts a unit production first, which makes
-- the description's first bit -- the OPCODE -- a `0`; see §4.
theTable : Table
theTable = rulesOf ntH ++ rulesOf ntB ++ rulesOf ntO
        ++ rulesOf ntS ++ rulesOf ntR ++ rulesOf ntE

-- ... and what it actually is, spelled out.  `refl`, so this is a
-- CHECK that the reification of `allRules` is the grammar as written in
-- `Quine.Base`'s comment, not a restatement of it.
_ : theTable ≡ ( unitP ntH c#            -- H → '#'
               ∷ unitP ntB c0            -- B → '0'
               ∷ unitP ntB c1            -- B → '1'
               ∷ unitP ntO c0            -- O → '0'
               ∷ unitP ntO c1            -- O → '1'
               ∷ binP ntO ntB ntE        -- O → B E
               ∷ binP ntS ntB ntR        -- S → B R
               ∷ binP ntR ntB ntR        -- R → B R
               ∷ binP ntR ntH ntE        -- R → H E
               ∷ binP ntE ntB ntO        -- E → B O
               ∷ [] )
_ = refl

-- ==================================================================
-- §2  THE CODEC.  Three bits a nonterminal, two a letter, one to say
--     which kind of production.  General for any CNF grammar over six
--     nonterminals and three letters -- nothing here is tuned to the
--     particular rules above.
-- ==================================================================

encNT : NT → String
encNT ntS = c0 ∷ c0 ∷ c0 ∷ []
encNT ntR = c0 ∷ c0 ∷ c1 ∷ []
encNT ntH = c0 ∷ c1 ∷ c0 ∷ []
encNT ntB = c0 ∷ c1 ∷ c1 ∷ []
encNT ntE = c1 ∷ c0 ∷ c0 ∷ []
encNT ntO = c1 ∷ c0 ∷ c1 ∷ []

encChr : Chr → String
encChr c0 = c0 ∷ c0 ∷ []
encChr c1 = c0 ∷ c1 ∷ []
encChr c# = c1 ∷ c0 ∷ []

encProd : Prod → String
encProd (unitP P c)  = c0 ∷ encNT P ++ encChr c
encProd (binP P Q T) = c1 ∷ encNT P ++ encNT Q ++ encNT T

encTable : Table → String
encTable []      = []
encTable (p ∷ t) = encProd p ++ encTable t

-- ... and back

nt3 : Chr → Chr → Chr → Maybe NT
nt3 c0 c0 c0 = just ntS
nt3 c0 c0 c1 = just ntR
nt3 c0 c1 c0 = just ntH
nt3 c0 c1 c1 = just ntB
nt3 c1 c0 c0 = just ntE
nt3 c1 c0 c1 = just ntO
nt3 _  _  _  = nothing

ch2 : Chr → Chr → Maybe Chr
ch2 c0 c0 = just c0
ch2 c0 c1 = just c1
ch2 c1 c0 = just c#
ch2 _  _  = nothing

consM : Prod → Maybe Table → Maybe Table
consM p nothing  = nothing
consM p (just t) = just (p ∷ t)

decProd : String → Maybe (Prod × String)
decProd (c0 ∷ a ∷ b ∷ c ∷ x ∷ y ∷ r) = mk (nt3 a b c) (ch2 x y)
  where mk : Maybe NT → Maybe Chr → Maybe (Prod × String)
        mk (just P) (just ch) = just (unitP P ch , r)
        mk _        _         = nothing
decProd (c1 ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ r) =
  mk (nt3 a b c) (nt3 d e f) (nt3 g h i)
  where mk : Maybe NT → Maybe NT → Maybe NT → Maybe (Prod × String)
        mk (just P) (just Q) (just T) = just (binP P Q T , r)
        mk _        _        _        = nothing
decProd _ = nothing

-- fuel, because a production is consumed but the recursion is not
-- structural; `length` is always enough, a production being ≥ 6 letters
decT : ℕ → String → Maybe Table
decT n       []      = just []
decT zero    (_ ∷ _) = nothing
decT (suc n) (x ∷ s) = go (decProd (x ∷ s))
  where go : Maybe (Prod × String) → Maybe Table
        go nothing        = nothing
        go (just (p , r)) = consM p (decT n r)

decTable : String → Maybe Table
decTable s = decT (length s) s

-- the codec IS a codec, at the table that matters
_ : decTable (encTable theTable) ≡ just theTable
_ = refl

-- ==================================================================
-- §3  THE PROGRAM.
--
--     metaSrc  =  ⌜theTable⌝  #  quote ⌜theTable⌝
--
-- 80 bits of description, a hash, and 160 letters of quoted
-- description: 241 characters, every one of them decided by the
-- decision procedure at typecheck time.
-- ==================================================================

theCode : String
theCode = encTable theTable

metaSrc : String
metaSrc = theCode ++ (c# ∷ enc theCode)

-- ==================================================================
-- §4  THE ROOT ACTION: print, AND read the grammar back.
--
-- `Interp` is parameterised by what a program does once its data has
-- been decoded; here it does both jobs at once, so ONE run of the
-- decision procedure settles the quine equation and the
-- self-description together.
-- ==================================================================

Out : Type₀
Out = String × Maybe Table

metaRoot : Chr → String → Out
metaRoot b d = emit b d , decTable d

module M = Interp Out ([] , nothing) metaRoot

-- ==================================================================
-- §5  THE FIXPOINT, checked.
--
--   left of the ↦ : the literal source text
--   right of it   : (its own text , the grammar that parsed it)
--
-- Both components of the answer mention only names introduced above --
-- `metaSrc` and `theTable` -- so nothing is written twice and nothing
-- can drift.
-- ==================================================================

metaQuine : passes (M.runOut ntS at (metaSrc ↦ just (metaSrc , just theTable) ∷ []))
metaQuine = refl

-- ... and the derivation itself, with `⌈_⌉` pinning the text: `⌈ metaSrc ⌉`
-- holds at exactly one world, and that world is the source.
metaDeriv : Deriv ntS metaSrc
metaDeriv = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) metaSrc refl

metaLit : ⌈ metaSrc ⌉ ⊢ Deriv ntS
metaLit = ⌈⌉-E metaDeriv

{-
  ------------------------------------------------------------------
  THE OBSTRUCTION, measured.

  The decision procedure is `löb` with no tabulation: `▷ Chart` is "the
  chart at every shorter string", which is the right well-founded
  structure but shares nothing between consultations.  On this grammar
  -- right-linear, so every wrong cut dies at the literal matcher -- the
  cost is empirically cubic in the length of the text:

        49 letters   ≈ 0.4 s
       121 letters   ≈ 6.5 s
       241 letters   ≈ 60 s        -- this file runs the decision twice,
                                   -- for `metaQuine` and `metaDeriv`,
                                   -- and elaborates in about 2 minutes

  A grammar rich enough to parse GRAMMAR DESCRIPTIONS (nonterminal
  names, arrows, alternation) needs perhaps 15-25 nonterminals, and its
  own description in any comparable encoding runs to several hundred
  bits; at 3 characters of source per bit that is a four-figure input,
  which this evaluator will not finish.  The missing ingredient is not
  an idea about quines, it is a TABULATED fixpoint -- the same gap
  `Instances.Spans.Examples` records.  With one, the meta-circular
  grammar-of-grammars is a straightforward extension of this file: the
  parse tree of the description already IS the rule table, and `decProd`
  is deleted.
-}
