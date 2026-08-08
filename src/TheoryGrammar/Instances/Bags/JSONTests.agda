{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE JSON DECISION, RUN. `Bags.JSON` claims that key-order independence
   is DEFINITIONAL: the object sort's tensor is interleaving, so a schema
   grammar accepts every key order because there is nothing else it could
   do. -}
module TheoryGrammar.Instances.Bags.JSONTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)

open import TheoryGrammar.Instances.Bags.JSON

-- The documents.  `tags` is the ORDERED part; `{...}` is the BAG.

tags : Val
tags = arrV (num 1 ∷ txt 2 ∷ [])

tagsRev : Val
tagsRev = arrV (txt 2 ∷ num 1 ∷ [])

-- { "id": 7, "tags": [1,"x"] }
docA : Val
docA = objV ((kId , num 7) ∷ (kTags , tags) ∷ [])

-- { "tags": [1,"x"], "id": 7 }   -- the SAME object, keys reordered
docB : Val
docB = objV ((kTags , tags) ∷ (kId , num 7) ∷ [])

-- { "id": 7, "tags": ["x",1] }   -- the ARRAY reordered: a different value
docC : Val
docC = objV ((kId , num 7) ∷ (kTags , tagsRev) ∷ [])

-- { "id": 7 }                    -- a key missing
docD : Val
docD = objV ((kId , num 7) ∷ [])

-- { "id": 7, "name": [1,"x"] }   -- the wrong key
docE : Val
docE = objV ((kId , num 7) ∷ (kName , tags) ∷ [])

-- { "id": "7", "tags": [1,"x"] } -- the wrong value type
docF : Val
docF = objV ((kId , txt 7) ∷ (kTags , tags) ∷ [])

-- { "id": 7, "tags": [1,"x"], "name": 3 }   -- an extra member
docG : Val
docG = objV ((kId , num 7) ∷ (kTags , tags) ∷ (kName , num 3) ∷ [])

-- (i) a small object parses (ii) the SAME object with the keys reordered
-- gives the same answer (iii) the invalid documents are refuted One
-- battery, one term, seven documents.

_ : passes (run (derives! val ntRec) at
             ( docA ↦ true      -- { id:7, tags:[1,"x"] }
             ∷ docB ↦ true      -- KEYS REORDERED -- the whole point
             ∷ docC ↦ false     -- array elements reordered
             ∷ docD ↦ false     -- `tags` missing
             ∷ docE ↦ false     -- wrong key
             ∷ docF ↦ false     -- `id` is not a number
             ∷ docG ↦ false     -- an extra member
             ∷ [] ))
_ = refl

-- ... and the pieces are decided at their own sorts, by the same chart.
-- `ntTags` is a VALUE nonterminal (a value that is an array), so this is
-- the ordered half on its own.
_ : passes (run (derives! val ntTags) at
             ( tags ↦ true ∷ tagsRev ↦ false ∷ num 1 ↦ false ∷ [] ))
_ = refl

_ : passes (run (derives! val ntNum) at
             ( num 7 ↦ true ∷ txt 7 ↦ false ∷ tags ↦ false ∷ [] ))
_ = refl

-- the object sort directly: the record BODY, as a bag of members
_ : passes (run (derives! obj ntRecBody) at
             ( ((kId , num 7) ∷ (kTags , tags) ∷ []) ↦ true
             ∷ ((kTags , tags) ∷ (kId , num 7) ∷ []) ↦ true    -- reordered
             ∷ ((kId , num 7) ∷ [])                  ↦ false
             ∷ [] ))
_ = refl

-- THREE KEYS, ALL SIX ORDERS. The schema `Rec3 = { id : Num , tags :
-- [Num,Txt] , name : Txt }` is the same two-slot rule nested once -- `{id}
-- ⊎ ({tags} ⊎ {name})` -- so the grammar has a preferred BRACKETING and no
-- preferred ORDER.

mId mTags mName : Key × Val
mId   = kId   , num 7
mTags = kTags , tags
mName = kName , txt 5

_ : passes (run (derives! val ntRec3) at
             ( objV (mId ∷ mTags ∷ mName ∷ []) ↦ true
             ∷ objV (mId ∷ mName ∷ mTags ∷ []) ↦ true
             ∷ objV (mTags ∷ mId ∷ mName ∷ []) ↦ true
             ∷ objV (mTags ∷ mName ∷ mId ∷ []) ↦ true
             ∷ objV (mName ∷ mId ∷ mTags ∷ []) ↦ true
             ∷ objV (mName ∷ mTags ∷ mId ∷ []) ↦ true
             -- ... and the failures are still failures
             ∷ objV (mId ∷ mTags ∷ [])         ↦ false   -- `name` missing
             ∷ objV (mId ∷ mId ∷ mName ∷ [])   ↦ false   -- duplicate key
             ∷ [] ))
_ = refl

-- ... AND THE ANSWERS ARE THEOREMS.

RecOf : Val → Type₀
RecOf = DerivAt (val , ntRec)

noRec : (v : Val) → run (derives! val ntRec) v ≡ false → (¬G RecOf) v
noRec = refute RecOf (¬G RecOf) (derives? val ntRec)

-- the well-formed record, and its parse tree
recA : RecOf docA
recA = witness RecOf (¬G RecOf) (derives? val ntRec) docA refl

-- ... and the SAME term at the reordered document.  Two parse trees at
-- two different carriers -- which is what "the same parse" has to mean
-- when the carrier is a list and the grammar is a bag.
recB : RecOf docB
recB = witness RecOf (¬G RecOf) (derives? val ntRec) docB refl

-- reordering the ARRAY is a genuine failure, and this is the proof
no-C : RecOf docC → E.⊥* {ℓ-zero}
no-C = noRec docC refl

no-D : RecOf docD → E.⊥* {ℓ-zero}
no-D = noRec docD refl

no-F : RecOf docF → E.⊥* {ℓ-zero}
no-F = noRec docF refl
