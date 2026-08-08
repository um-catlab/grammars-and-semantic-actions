{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE META-CIRCULAR QUINE: a text that parses itself AND says what grammar
   it was parsed by. -}
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

-- §1 THE GRAMMAR, REIFIED. `Rule P` is the description's own notion of
-- production, and `allRules`/`allComplete` are the finite table the
-- decision procedure consumes.

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

-- §2 THE CODEC. Three bits a nonterminal, two a letter, one to say which
-- kind of production.

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

-- §3 THE PROGRAM. metaSrc = ⌜theTable⌝ # quote ⌜theTable⌝ 80 bits of
-- description, a hash, and 160 letters of quoted description: 241
-- characters, every one of them decided by the decision procedure at
-- typecheck time.

theCode : String
theCode = encTable theTable

metaSrc : String
metaSrc = theCode ++ (c# ∷ enc theCode)

-- §4 THE ROOT ACTION: print, AND read the grammar back.

Out : Type₀
Out = String × Maybe Table

metaRoot : Chr → String → Out
metaRoot b d = emit b d , decTable d

module M = Interp Out ([] , nothing) metaRoot

-- §5 THE FIXPOINT, checked. left of the ↦ : the literal source text right
-- of it : (its own text , the grammar that parsed it) Both components of
-- the answer mention only names introduced above -- `metaSrc` and
-- `theTable` -- so nothing is written twice and nothing can drift.

metaQuine : passes (M.runOut ntS at (metaSrc ↦ just (metaSrc , just theTable) ∷ []))
metaQuine = refl

-- ... and the derivation itself, with `⌈_⌉` pinning the text: `⌈ metaSrc ⌉`
-- holds at exactly one world, and that world is the source.
metaDeriv : Deriv ntS metaSrc
metaDeriv = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) metaSrc refl

metaLit : ⌈ metaSrc ⌉ ⊢ Deriv ntS
metaLit = ⌈⌉-E metaDeriv

{- THE OBSTRUCTION, measured. The decision procedure is `löb` with no
   tabulation: `▷ Chart` is "the chart at every shorter string", which is
   the right well-founded structure but shares nothing between
   consultations. -}
