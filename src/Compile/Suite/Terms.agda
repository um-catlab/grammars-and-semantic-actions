{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CORPUS: closed linear λ-terms to run the backends on.

  WHY NOT `TheoryGrammar.Generate.genμ`.  That generator produces
  elements of `μ F ix`, and `Tm : Usage → Type₀`
  (`Instances/LinLam/Syntax.agda`) is a plain `data`, not a `μ` over
  `linFib`.  It cannot cheaply become one: `Inductive.Functor` has five
  formers (`⌜_⌝`, `Var`, `⊕e`, `&e`, `⊗e`) and only `⊗e` moves the
  world, along `Fib .parts`.  `monoidSig`'s `UseParts` never yields
  `true ∷ u`, so `tlam : Tm (true ∷ u) → Tm u` -- a recursive position
  at a WEAKENED world, i.e. `Opt.BodyOf` -- has no code.  Presenting
  `Tm` as a `μ` therefore means a new `Fibered λSig` whose `lamOp`
  `parts` IS weakening (the move `Instances/LinLam/DB.agda` makes for de
  Bruijn terms), plus `Listed` splittings, plus a `foldC` back to `Tm`:
  roughly 150 lines of new framework-adjacent code.  That is a real and
  worthwhile piece of work, and it is not this harness.

  WHAT IS REUSED.  The randomness is `Generate`'s and not a new one:
  `Seed`, `next`, `mix`, `sample`, `stream`, `catMaybes` are imported
  from `TheoryGrammar.Generate`, so a draw here is the same LCG, the
  same Knuth mix, and the same "a generator that offers nothing does not
  get to pretend otherwise" as `GenerateTests.sample₁`.  What is local
  is the SEARCH SPACE: `genTm`, a depth-bounded exhaustive enumeration
  of `Tm u`, which is `genμ`'s `genLayer` written by hand at this one
  inductive type.

  PHASE.  Phase 1, and marked: `genTm` matches on the usage and on
  `Use⊎`, exactly as a description's `Seek (Fib .Split o)` would.
-}
open import Cubical.Foundations.Prelude

module Compile.Suite.Terms where

open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; map; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)

open import Compile.ClosureConv.Convert
  using ( Tm; tvar; tapp; tlam
        ; Usage; Use⊎; unil; uleft; uright; uskip; Empty; Solo
        ; idLin; selfApp; appLin; bigT; applyK; Kterm )

open import TheoryGrammar.Generate
  using (Seed; next; mix; sample; stream; seeds; catMaybes; bindL)

-- ==================================================================
-- §1  THE TWO SIDE CONDITIONS, DECIDED.
--
-- `Solo` and `Empty` are RECURSIVE PREDICATES on the usage, so their
-- witnesses are computed, not searched: at most one each.
-- ==================================================================

emptyW : (u : Usage) → Maybe (Empty u)
emptyW []          = just tt
emptyW (true  ∷ _) = nothing
emptyW (false ∷ u) = emptyW u

soloW : (u : Usage) → Maybe (Solo u)
soloW []          = nothing
soloW (true  ∷ u) = emptyW u      -- `Solo (true ∷ u)` IS `Empty u`
soloW (false ∷ u) = soloW u

mList : {A : Type₀} → Maybe A → List A
mList nothing  = []
mList (just a) = a ∷ []

-- ==================================================================
-- §2  THE SPLITTINGS, ENUMERATED.
--
-- This is `Seek (linFib .Split appop)` -- `Generate`'s one theory
-- obligation -- written out.  `2^(live u)` of them, and `uskip` is why
-- a dead slot costs no branching.
-- ==================================================================

Split3 : Usage → Type₀
Split3 u = Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ] Use⊎ u₁ u₂ u

allSplits : (u : Usage) → List (Split3 u)
allSplits []          = ([] , [] , unil) ∷ []
allSplits (true  ∷ u) =
     map (λ z → true  ∷ z .fst , false ∷ z .snd .fst , uleft  (z .snd .snd))
         (allSplits u)
  ++ map (λ z → false ∷ z .fst , true  ∷ z .snd .fst , uright (z .snd .snd))
         (allSplits u)
allSplits (false ∷ u) =
     map (λ z → false ∷ z .fst , false ∷ z .snd .fst , uskip  (z .snd .snd))
         (allSplits u)

-- ==================================================================
-- §3  THE SEARCH SPACE.  Depth-bounded, exhaustive, and INTRINSICALLY
-- linear: every element of `genTm n u` is a term at usage `u`, so a
-- generated closed term is closed and linear by construction.  There
-- is no filter and no well-formedness check anywhere in this file.
-- ==================================================================

genTm : ℕ → (u : Usage) → List (Tm u)
genTm zero    u = []
genTm (suc n) u =
     map tvar (mList (soloW u))
  ++ map tlam (genTm n (true ∷ u))
  ++ bindL (allSplits u) (λ z →
       bindL (genTm n (z .fst)) (λ a →
         map (λ b → tapp (z .snd .snd) a b) (genTm n (z .snd .fst))))

closedTms : ℕ → List (Tm [])
closedTms n = genTm n []

-- ==================================================================
-- §4  DRAWING.  `Generate.stream` is the fuzzer's own draw.
-- ==================================================================

drawTms : ℕ → ℕ → Seed → List (Tm [])
drawTms depth count s = catMaybes (stream count (closedTms depth) s)

-- ==================================================================
-- §5  NAMING, so the table has a first column.
-- ==================================================================

nameFrom : ℕ → List (Tm []) → List (String × Tm [])
nameFrom _ []       = []
nameFrom i (t ∷ ts) =
  (primStringAppend "g" (primShowNat i) , t) ∷ nameFrom (suc i) ts

-- the four terms the backends' own `refl` tests are pinned at, plus
-- the two auxiliaries they are built from
corpus : List (String × Tm [])
corpus =
    ("idLin"   , idLin)
  ∷ ("selfApp" , selfApp)
  ∷ ("appLin"  , appLin)
  ∷ ("Kterm"   , Kterm)
  ∷ ("bigT"    , bigT)
  ∷ ("applyK"  , applyK)
  ∷ []

-- `depth` bounds the HEIGHT of the term, `count` the number of draws.
drawn : ℕ → ℕ → Seed → List (String × Tm [])
drawn depth count s = nameFrom 0 (drawTms depth count s)

suite : ℕ → ℕ → Seed → List (String × Tm [])
suite depth count s = corpus ++ drawn depth count s

-- ==================================================================
-- §6  IT COMPUTES, AND THE SPACE IS THE EXPECTED ONE.
-- ==================================================================

_ : length (allSplits (true ∷ false ∷ true ∷ [])) ≡ 4
_ = refl

_ : closedTms 2 ≡ idLin ∷ []
_ = refl

_ : closedTms 3 ≡ idLin ∷ selfApp ∷ []
_ = refl

_ : length (closedTms 4) ≡ 9
_ = refl
