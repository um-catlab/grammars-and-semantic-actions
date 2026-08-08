{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE TEST SUITE, WITH ITS INPUTS DRAWN BY `TheoryGrammar.Generate`.

  `Generate` is the dual of `Decidable.Inductive`: that one DECIDES
  `μ F i`, this one PRODUCES elements of it.  Pointed at the same
  description `Chain.Paren.Grammar.parenF`, it becomes a fuzzer for THIS
  language -- and the draws are not candidate strings to be filtered,
  they are

      Draw parenF ntm  =  a token list TOGETHER WITH its derivation

  so every generated input is grammatical BY CONSTRUCTION.  There is no
  rejection step and no generate-and-test.

  ==================================================================
  WHAT IS ACTUALLY BEING TESTED, since "it parses" is a tautology here.

  The property is `Chain.Paren.Quote`'s idempotence, at inputs nobody
  chose:

      requote (quote t)  ≡  just (quote t)

  -- print the tree, re-parse the printed form, print THAT, and get the
  same text.  It exercises the parser and the printer against each
  other, and a disagreement in either would break it.  `Quote` checks it
  on five hand-picked shapes; this checks it on whatever the generator
  draws.

  Stated on TOKEN LISTS rather than on trees deliberately: `NTm` has no
  decidable equality here, and the token list is the observable the two
  passes have to agree about anyway.

  ==================================================================
  THE NAME POOL is the fuzzer's one input specific to this language.
  `UpDesc (⌜ B ⌝)` asks for a list of WORLDS-WITH-WITNESSES, and for
  `VarTok`/`Binder` that is exactly "which identifiers may appear".
  Three names, so shadowing is drawn often.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Fuzz where

open import Cubical.Data.Bool using (Bool; true; false; _and_)
open import Cubical.Data.List using (List; []; _∷_; _++_; map; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt; tt*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Graded using (fib)
open import TheoryGrammar.Generate
  using (StrictPoint; opU; splitU; partsU; Seed; catMaybes)

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar
open import Chain.Paren.Elab
open import Chain.Paren.Quote

open import TheoryGrammar.Generate.Suite

-- ==================================================================
-- §1  THE THEORY'S OBLIGATION FOR GENERATION: a STRICT point.
--
-- `GenerateTests.strictStrPoint`, at this alphabet.  Concatenation is
-- total, its canonical splitting is `splitAll`, and `partsU` is
-- `Eq.refl` because `MonParts` reduces on a constructor.
-- ==================================================================

strictStrPoint : StrictPoint (strGraded .fib)
strictStrPoint .opU nilop _ = []
strictStrPoint .opU appop f = f true ++ f false
strictStrPoint .splitU nilop f = tt
strictStrPoint .splitU appop f = f true , f false , splitAll (f true) (f false)
strictStrPoint .partsU nilop f ()
strictStrPoint .partsU appop f true  = Eq.refl
strictStrPoint .partsU appop f false = Eq.refl

-- AT `strGraded .fib`, NOT at `strFib`.  `DecInd` (which `Grammar`
-- opened) instantiates `Ind` at the graded record's field, so writing
-- `strFib` here would give a second `Ind` application and `parenF`
-- would not typecheck against it.
open FuzzSuite (strGraded .fib) ℓ-zero NT (λ _ → tt)
  (λ o m _ → enumSplit o m) enumArL
  using (UpDesc; Draw; draws; world; viaA)

-- ==================================================================
-- §2  THE FUZZER'S DESCRIPTION.  Each constant carries the WORLD it
-- lives at; the alternatives carry their weight by multiplicity.
-- ==================================================================

-- the identifiers the fuzzer may draw
namePool : List Name
namePool = ('x' ∷ []) ∷ ('y' ∷ []) ∷ ('f' ∷ []) ∷ []

varWorlds : List (Σ[ m ∈ String ] VarTok m)
varWorlds = map (λ n → (tid n ∷ []) , (n , Eq.refl)) namePool

binderWorlds : List (Σ[ m ∈ String ] Binder m)
binderWorlds = map (λ n → (tlam ∷ tid n ∷ tdot ∷ []) , (n , Eq.refl)) namePool

litWorld : (t : Tok) → List (Σ[ m ∈ String ] ⌈ t ∷ [] ⌉ m)
litWorld t = ((t ∷ []) , Eq.refl) ∷ []

parenUp : (x : NT) → UpDesc (parenF x)
parenUp ntm = altsT , up
  where
  -- the weights: a variable twice, so the recursion terminates often
  altsT : List AltT
  altsT = aVar ∷ aVar ∷ aLam ∷ aApp ∷ aAnn ∷ aPar ∷ []

  up : (a : AltT) → UpDesc (bodyT a)
  up aVar = lift varWorlds
  up aLam = uL
    where uL : (b : Bool) → UpDesc (lamF b)
          uL true  = lift binderWorlds
          uL false = tt*
  up aApp = u₁
    where u₃ : (b : Bool) → UpDesc (app₃ b)
          u₃ true  = tt*
          u₃ false = lift (litWorld trp)
          u₂ : (b : Bool) → UpDesc (app₂ b)
          u₂ true  = tt*
          u₂ false = u₃
          u₁ : (b : Bool) → UpDesc (app₁ b)
          u₁ true  = lift (litWorld tlp)
          u₁ false = u₂
  up aAnn = v₁
    where v₄ : (b : Bool) → UpDesc (ann₄ b)
          v₄ true  = tt*
          v₄ false = lift (litWorld trp)
          v₃ : (b : Bool) → UpDesc (ann₃ b)
          v₃ true  = lift (litWorld tcolon)
          v₃ false = v₄
          v₂ : (b : Bool) → UpDesc (ann₂ b)
          v₂ true  = tt*
          v₂ false = v₃
          v₁ : (b : Bool) → UpDesc (ann₁ b)
          v₁ true  = lift (litWorld tlp)
          v₁ false = v₂
  up aPar = w₁
    where w₂ : (b : Bool) → UpDesc (par₂ b)
          w₂ true  = tt*
          w₂ false = lift (litWorld trp)
          w₁ : (b : Bool) → UpDesc (par₁ b)
          w₁ true  = lift (litWorld tlp)
          w₁ false = w₂

parenUp nty = altsY , up
  where
  altsY : List AltY
  altsY = yBase ∷ yBase ∷ yArr ∷ []

  up : (a : AltY) → UpDesc (bodyY a)
  up yBase = lift (litWorld tbase)
  up yArr  = r₁
    where r₄ : (b : Bool) → UpDesc (arr₄ b)
          r₄ true  = tt*
          r₄ false = lift (litWorld trp)
          r₃ : (b : Bool) → UpDesc (arr₃ b)
          r₃ true  = lift (litWorld tarrow)
          r₃ false = r₄
          r₂ : (b : Bool) → UpDesc (arr₂ b)
          r₂ true  = tt*
          r₂ false = r₃
          r₁ : (b : Bool) → UpDesc (arr₁ b)
          r₁ true  = lift (litWorld tlp)
          r₁ false = r₂

-- ==================================================================
-- §3  THE DRAWS.  A word together with its parse tree.
-- ==================================================================

fuzzDraws : (size count : ℕ) → Seed → List (Draw parenF ntm)
fuzzDraws size count sd = draws parenF strictStrPoint parenUp size count ntm sd

fuzzWords : (size count : ℕ) → Seed → List String
fuzzWords size count sd = map (world parenF ntm) (fuzzDraws size count sd)

-- ==================================================================
-- §4  THE PROPERTY, ON EVERY DRAW.
--
-- `requote (quote t) ≡ just (quote t)` -- print, re-parse, print again,
-- and get the same text.  Stated at token lists because that is the
-- observable the parser and the printer must agree about.
-- ==================================================================

tokEq : String → String → Bool
tokEq u v with decEqS u v
... | inl _ = true
... | inr _ = false

-- print a derivation, re-parse the print, and print THAT
requote : String → Maybe String
requote ts with parseTrm ts tt
... | inr _ = nothing
... | inl d = just (printTrm ts d .fst)

stable? : Maybe String → String → Bool
stable? (just u) v = tokEq u v
stable? nothing  v = false

-- the printed form of a draw, and whether it survives a round trip
printedOf : Draw parenF ntm → String
printedOf = viaA parenF ntm (printTrm)

roundTrips : Draw parenF ntm → Bool
roundTrips d = stable? (requote (printedOf d)) (printedOf d)

allTrue : List Bool → Bool
allTrue []           = true
allTrue (true  ∷ bs) = allTrue bs
allTrue (false ∷ _)  = false

-- THE FUZZ TEST.  Every draw's printed form re-parses to the same text.
idemOn : (size count : ℕ) → Seed → Bool
idemOn size count sd = allTrue (map roundTrips (fuzzDraws size count sd))

-- ==================================================================
-- §5  RUN IT.  Small parameters: `decμ` enumerates splittings, so the
-- reparse is superlinear and the sizes here are what evaluates.
-- ==================================================================

_ : idemOn 6 8 2024 ≡ true
_ = refl

_ : idemOn 6 8 7 ≡ true
_ = refl

_ : idemOn 6 8 99 ≡ true
_ = refl

-- ==================================================================
-- §6  NON-VACUITY.  `allTrue []` is `true`, so the tests above would
-- pass on an empty draw list.  These pin that the generator actually
-- produced words, and that they are not all one token.
-- ==================================================================

nonEmpty : {A : Type₀} → List A → Bool
nonEmpty []      = false
nonEmpty (_ ∷ _) = true

totalLen : List String → ℕ
totalLen []       = 0
totalLen (w ∷ ws) = length w + totalLen ws

lessThan : ℕ → ℕ → Bool
lessThan zero    _       = true
lessThan (suc _) zero    = false
lessThan (suc a) (suc b) = lessThan a b

_ : nonEmpty (fuzzDraws 6 8 2024) ≡ true
_ = refl

_ : nonEmpty (fuzzDraws 6 8 99) ≡ true
_ = refl

-- ... and the words carry REAL STRUCTURE: more than twenty tokens
-- across the eight draws, where size 3 gave only three.  Without this
-- the suite above would pass on a list of single identifiers.
_ : lessThan 20 (totalLen (fuzzWords 6 8 2024)) ≡ true
_ = refl


