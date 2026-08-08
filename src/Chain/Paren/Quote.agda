{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  QUOTING A SEMANTIC VALUE BACK, AND THE IDEMPOTENCE THAT IS THE POINT.

  A semantic action reads a value out of a derivation:

      act : A ⊢ Δ X

  and the question this file answers is what it means for that action to
  be FAITHFUL.  Not that it is injective on worlds -- it is not, and
  should not be: erasing the parentheses changes the underlying token
  string and leaves the tree alone, which is the whole reason for the
  action.  What can be asked is that the value QUOTES BACK to a world
  the action reads the same way:

      quote : X → Car s          a canonical world for the value
      idem  : act (quote (act d)) ≡ act d

  -- the action is idempotent THROUGH the quote, even though the world
  is not fixed.  Print the tree, re-parse it, get that tree.

  ==================================================================
  THIS IS `Chain.Project`'s DISTINCTION, ARRIVING FROM THE OTHER SIDE.

  There, `Section` was `fwd ∘ bwd ≡ id` (every object survives a
  round trip) and `Reflects` was `fwd ∘ bwd ∘ fwd ≡ fwd` (every object
  THE PASS PRODUCED survives).  `idem` above is `Reflects`, and the
  reason to want the weak one is exactly the reason given there: with an
  AMBIGUOUS surface syntax `bwd` cannot be injective, so two derivations
  share one printed form and at most one survives.

  AND THAT IS WHAT CHANGED.  `Chain.PrintTests.notInjective` REFUTES the
  property for `Lambda.Parse`'s grammar -- `λx. (x x) x` and
  `λx. x (x x)` have one printed form there, because application was
  bare juxtaposition.  `Chain.Paren.Grammar` parenthesises it, and §3
  below is the same statement HOLDING, on the same shapes.  The
  parenthesisation was not a convenience; it is what makes the action
  quotable.

  ==================================================================
  PRINTING IS ITSELF A SEMANTIC ACTION.  `printAlg` is a `SynAlg` like
  any other, so the printer is not a traversal of a syntax tree -- it is
  another consumer of the same fold, and `Chain.Paren.Elab`'s point
  ("each pass takes in the action of the phase before it") applies to it
  unchanged.  `quoteN` is the same algebra read at `NTm`, which is what
  a round-trip statement needs to name both ends.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Quote where

open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sum using (inl; inr)

open import Agda.Builtin.String using () renaming (String to UString)

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar
open import Chain.Paren.Elab

open import TheoryGrammar.SemanticAction
open ActFib strFib using (Δ)

-- ==================================================================
-- §1  THE QUOTE.  A canonical, fully parenthesised token string --
-- and it is a `SynAlg`, i.e. the same fold at another carrier.
-- ==================================================================

printAlg : SynAlg (List Tok) (List Tok)
printAlg .varA n   = tid n ∷ []
printAlg .lamA n b = tlp ∷ tlam ∷ tid n ∷ tdot ∷ (b ++ (trp ∷ []))
printAlg .appA f a = tlp ∷ (f ++ (a ++ (trp ∷ [])))
printAlg .annA t T = tlp ∷ (t ++ (tcolon ∷ (T ++ (trp ∷ []))))
printAlg .baseA    = tbase ∷ []
printAlg .arrA a b = tlp ∷ (a ++ (tarrow ∷ (b ++ (trp ∷ []))))

-- the printer, straight off a derivation -- no tree in between
printTrm : Trm ⊢ Δ (List Tok)
printTrm = readWith printAlg

-- ... and the same algebra read at the named tree, which is what a
-- round-trip statement needs in order to name both ends
quoteN : NTm → List Tok
quoteN (nvar n)   = printAlg .varA n
quoteN (nlam n b) = printAlg .lamA n (quoteN b)
quoteN (napp f a) = printAlg .appA (quoteN f) (quoteN a)
quoteN (nann t T) = printAlg .annA (quoteN t) (quoteY T)
  where quoteY : NTy → List Tok
        quoteY nbase       = printAlg .baseA
        quoteY (narr a b)  = printAlg .arrA (quoteY a) (quoteY b)

-- ==================================================================
-- §2  THE ACTION, EXTERNALISED ONCE.
-- ==================================================================

-- PRIMITIVE (phase 1): the exit.  The `inr` branch discards a
-- REFUTATION that the token stream is a term.
readNamed : List Tok → Maybe NTm
readNamed ts with parseTrm ts tt
... | inr _ = nothing
... | inl d = just (toNamed ts d .fst)

-- ==================================================================
-- §3  IDEMPOTENCE.  Print the tree, re-parse it, get THAT TREE.
--
-- The general statement, and then it checked on the shapes
-- `Chain.PrintTests` used to REFUTE it with.
-- ==================================================================

-- the property, named: every tree the action produced quotes back to a
-- world the action reads the same way
Idem : Type₀
Idem = (ts : List Tok) (t : NTm) → readNamed ts ≡ just t
     → readNamed (quoteN t) ≡ just t

vX vF vA : Name
vX = 'x' ∷ []
vF = 'f' ∷ []
vA = 'a' ∷ []

-- ---- the two shapes `notInjective` used ----------------------------
-- `\x. ((x x) x)` and `\x. (x (x x))`.  Under `Lambda.Parse` these had
-- ONE printed form ("λx. x x x") and the property was refuted.  Here
-- they print differently and each round-trips.

leftA rightA : NTm
leftA  = nlam vX (napp (napp (nvar vX) (nvar vX)) (nvar vX))
rightA = nlam vX (napp (nvar vX) (napp (nvar vX) (nvar vX)))

-- the printed forms are DIFFERENT -- this is the parenthesisation doing
-- the work that was missing
_ : quoteN leftA ≡
    tlp ∷ tlam ∷ tid vX ∷ tdot
  ∷ tlp ∷ tlp ∷ tid vX ∷ tid vX ∷ trp ∷ tid vX ∷ trp ∷ trp ∷ []
_ = refl

_ : quoteN rightA ≡
    tlp ∷ tlam ∷ tid vX ∷ tdot
  ∷ tlp ∷ tid vX ∷ tlp ∷ tid vX ∷ tid vX ∷ trp ∷ trp ∷ trp ∷ []
_ = refl

-- ... and each round-trips to ITSELF
_ : readNamed (quoteN leftA)  ≡ just leftA
_ = refl

_ : readNamed (quoteN rightA) ≡ just rightA
_ = refl

-- ---- and on the rest of the language --------------------------------
idN : NTm
idN = nlam vX (nvar vX)

_ : readNamed (quoteN idN) ≡ just idN
_ = refl

shadowN : NTm                                     -- \x. \x. x
shadowN = nlam vX (nlam vX (nvar vX))

_ : readNamed (quoteN shadowN) ≡ just shadowN
_ = refl

annN : NTm                                        -- ((\x. x) : (o -o o))
annN = nann (nlam vX (nvar vX)) (narr nbase nbase)

_ : readNamed (quoteN annN) ≡ just annN
_ = refl

appN : NTm                                        -- \f. \a. (f a)
appN = nlam vF (nlam vA (napp (nvar vF) (nvar vA)))

_ : readNamed (quoteN appN) ≡ just appN
_ = refl

-- ==================================================================
-- §4  AND THE CONCRETE ELEMENT REALLY DOES CHANGE.
--
-- This is the half that makes `Idem` the right statement rather than a
-- statement about worlds: the token string is NOT preserved -- the
-- quote normalises the parentheses -- while the tree is.
-- ==================================================================

-- `\x. x` with no parentheses parses ...
bareToks : List Tok
bareToks = tlam ∷ tid vX ∷ tdot ∷ tid vX ∷ []

_ : readNamed bareToks ≡ just idN
_ = refl

-- ... and quotes back PARENTHESISED, so the world moved
_ : quoteN idN ≡ tlp ∷ tlam ∷ tid vX ∷ tdot ∷ tid vX ∷ trp ∷ []
_ = refl

-- ... and the two token strings really are different, proved and not
-- merely asserted: one begins with `\` and the other with `(`.
private
  isLam : List Tok → Bool
  isLam (tlam ∷ _) = true
  isLam _          = false

worldMoved : (bareToks ≡ quoteN idN) → E.⊥
worldMoved p = true≢false (cong isLam p)

-- ... and the ACTION does not notice, which is exactly `Idem`
actionStable : readNamed bareToks ≡ readNamed (quoteN idN)
actionStable = refl
