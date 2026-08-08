{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A CONCURRENT QUINE -- the quine, in the theory of TRACES. -}
module TheoryGrammar.Quine.Trace where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Fibered using (Fibered)
open import TheoryGrammar.Enumerable using (No; decΠBool; _∈L_; here; there)
open import TheoryGrammar.SemanticAction using (module ActInd)
open import TheoryGrammar.Decidable.Representable using (module DecRep)
import TheoryGrammar.Decidable.Enumerated as DE

import TheoryGrammar.Instances.Traces.Protocol as Pr
open Pr using ( Sid; s₀; s₁; Act; opn; msg; cls; Ev; Ind
              ; decInd; isPropInd; ⊤I; dec⊤I; isProp⊤I )

-- §0 THE ALPHABET, REUSED. `Protocol`'s two sessions and three actions,
-- read as the tiny quine language's letters.

Wd : Type₀
Wd = List Ev

a0 a1 hsh b0 b1 : Ev
a0  = s₀ , opn        -- code bit 0, session 0
a1  = s₀ , msg        -- code bit 1, session 0
hsh = s₀ , cls        -- the hash,   session 0
b0  = s₁ , opn        -- data bit 0, session 1
b1  = s₁ , msg        -- data bit 1, session 1

-- §1 THE GRAMMAR. `Quine.Base`'s, plus `D` -- over strings the code and
-- the data were the same two letters and `#` told them apart; here the
-- SESSION tells them apart, so the two bit classes are two nonterminals
-- and the hash has become an ordering marker rather than a separator.

data QNT : Type₀ where ntS ntR ntH ntB ntE ntO ntD : QNT

-- The terminal productions. Stated as `Eq`-equations (`Protocol`'s idiom)
-- rather than as a type family on letters: matching `Eq.refl` determines
-- the letter, which is what makes `qallComplete` twenty lines instead of
-- ninety.
qunitR : QNT → Ev → Type₀
qunitR ntS e = ⊥
qunitR ntR e = ⊥
qunitR ntE e = ⊥
qunitR ntH e = e Eq.≡ hsh
qunitR ntB e = (e Eq.≡ a0) ⊎ (e Eq.≡ a1)
qunitR ntO e = (e Eq.≡ b0) ⊎ (e Eq.≡ b1)
qunitR ntD e = (e Eq.≡ b0) ⊎ (e Eq.≡ b1)

-- The binary productions, indexed: `BinIx P` says HOW MANY a nonterminal
-- has and `blhs`/`brhs` name the two children.
BinIx : QNT → Type₀
BinIx ntS = Unit
BinIx ntR = Bool
BinIx ntE = Unit
BinIx ntO = Unit
BinIx ntH = ⊥
BinIx ntB = ⊥
BinIx ntD = ⊥

blhs : (P : QNT) → BinIx P → QNT
blhs ntS tt    = ntB            -- S → B R
blhs ntR true  = ntB            -- R → B R
blhs ntR false = ntH            -- R → H E
blhs ntE tt    = ntD            -- E → D O
blhs ntO tt    = ntD            -- O → D E
blhs ntH ()
blhs ntB ()
blhs ntD ()

brhs : (P : QNT) → BinIx P → QNT
brhs ntS tt    = ntR
brhs ntR true  = ntR
brhs ntR false = ntE
brhs ntE tt    = ntO
brhs ntO tt    = ntE
brhs ntH ()
brhs ntB ()
brhs ntD ()

qbinR : QNT → QNT → QNT → Type₀
qbinR P Q T = Σ[ k ∈ BinIx P ] ((Q Eq.≡ blhs P k) × (T Eq.≡ brhs P k))

-- §2 THE INTERPRETER, as a semantic action.

Val : QNT → Type₀
Val ntS = Wd × Wd                 -- THE OUTPUT: what each session prints
Val ntR = List Bool               -- dec of the data
Val ntH = Unit
Val ntB = Bool                    -- the code bit
Val ntE = List Bool               -- dec of the data below
Val ntO = List Bool               -- dec of the data below
Val ntD = Bool                    -- the data bit

-- QUOTING: the only word function in the interpreter, and it is the
-- classical quine's `quote`.
enc : List Bool → List Bool
enc []      = []
enc (b ∷ d) = b ∷ b ∷ enc d

-- the two renderings of a bit string: as session-0 code, and as
-- session-1 data.  Transliteration, not computation.
codeW : List Bool → Wd
codeW []      = []
codeW (b ∷ d) = (if b then a1 else a0) ∷ codeW d

dataW : List Bool → Wd
dataW []      = []
dataW (b ∷ d) = (if b then b1 else b0) ∷ dataW d

-- THE OPCODE'S MEANING. `emit b d` is the PAIR of streams a program with
-- opcode `b` and decoded data `d` prints.
emit : Bool → List Bool → Wd × Wd
emit false d = (codeW d ++ hsh ∷ [] , dataW (enc d))   -- code, then hash
emit true  d = (hsh ∷ codeW d       , dataW (enc d))   -- hash, then code

unitVal : (P : QNT) (e : Ev) → qunitR P e → Val P
unitVal ntS e ()
unitVal ntR e ()
unitVal ntE e ()
unitVal ntH e Eq.refl       = tt
unitVal ntB e (inl Eq.refl) = false          -- the code bit itself
unitVal ntB e (inr Eq.refl) = true
unitVal ntD e (inl Eq.refl) = false          -- the data bit itself
unitVal ntD e (inr Eq.refl) = true
unitVal ntO e _             = []             -- a pair's second bit: dropped

binVal : (P Q T : QNT) → qbinR P Q T → Val Q → Val T → Val P
binVal ntS Q T (tt    , Eq.refl , Eq.refl) b d = emit b d   -- run the opcode
binVal ntR Q T (true  , Eq.refl , Eq.refl) _ d = d          -- skip a code bit
binVal ntR Q T (false , Eq.refl , Eq.refl) _ d = d          -- the data
binVal ntE Q T (tt    , Eq.refl , Eq.refl) b d = b ∷ d      -- KEEP the first
binVal ntO Q T (tt    , Eq.refl , Eq.refl) _ d = d          -- DROP the second
binVal ntH Q T (() , _)
binVal ntB Q T (() , _)
binVal ntD Q T (() , _)

-- §3 EVERYTHING ELSE, OVER AN ARBITRARY INDEPENDENCE RELATION.

module Over (I : Ev → Ev → Type₀)
            (decI : (e f : Ev) → I e f ⊎ No (I e f))
            (isPropI : (e f : Ev) → isProp (I e f)) where

  open Pr.Over I decI isPropI public

  -- THE PARSE TREES.  `Protocol.Over.CYK` at this grammar.
  module C = CYK QNT qunitR qbinR

  qallRules : (P : QNT) → List (C.Rule P)
  qallRules ntS = inr (ntB , ntR , (tt    , Eq.refl , Eq.refl)) ∷ []
  qallRules ntR = inr (ntB , ntR , (true  , Eq.refl , Eq.refl))
                ∷ inr (ntH , ntE , (false , Eq.refl , Eq.refl)) ∷ []
  qallRules ntH = inl (hsh , Eq.refl) ∷ []
  qallRules ntB = inl (a0 , inl Eq.refl) ∷ inl (a1 , inr Eq.refl) ∷ []
  qallRules ntE = inr (ntD , ntO , (tt    , Eq.refl , Eq.refl)) ∷ []
  qallRules ntO = inl (b0 , inl Eq.refl) ∷ inl (b1 , inr Eq.refl)
                ∷ inr (ntD , ntE , (tt    , Eq.refl , Eq.refl)) ∷ []
  qallRules ntD = inl (b0 , inl Eq.refl) ∷ inl (b1 , inr Eq.refl) ∷ []

  qallComplete : (P : QNT) (r : C.Rule P) → r ∈L qallRules P
  qallComplete ntS (inl (e , ()))
  qallComplete ntS (inr (Q , T , (tt    , Eq.refl , Eq.refl))) = here
  qallComplete ntR (inl (e , ()))
  qallComplete ntR (inr (Q , T , (true  , Eq.refl , Eq.refl))) = here
  qallComplete ntR (inr (Q , T , (false , Eq.refl , Eq.refl))) = there here
  qallComplete ntH (inl (e , Eq.refl))                         = here
  qallComplete ntH (inr (Q , T , (() , _)))
  qallComplete ntB (inl (e , inl Eq.refl))                     = here
  qallComplete ntB (inl (e , inr Eq.refl))                     = there here
  qallComplete ntB (inr (Q , T , (() , _)))
  qallComplete ntE (inl (e , ()))
  qallComplete ntE (inr (Q , T , (tt    , Eq.refl , Eq.refl))) = here
  qallComplete ntO (inl (e , inl Eq.refl))                     = here
  qallComplete ntO (inl (e , inr Eq.refl))                     = there here
  qallComplete ntO (inr (Q , T , (tt    , Eq.refl , Eq.refl))) = there (there here)
  qallComplete ntD (inl (e , inl Eq.refl))                     = here
  qallComplete ntD (inl (e , inr Eq.refl))                     = there here
  qallComplete ntD (inr (Q , T , (() , _)))

  module CD = C.Decide qallRules qallComplete litProbe

  -- The interpreter, as a term.  `Quine.Base.Interp` verbatim, with
  -- `strFib` replaced by `trFib` and the grammar replaced by this one.

  module AI = ActInd trFib ℓ-zero QNT (λ _ → tt)

  Mot : C.G.Ix → Type₀
  Mot i = Δ (Val (i .fst)) (i .snd)

  alg : AI.ActAlg C.CYKF Val
  alg P = ⊕ᴰ-E branch
    where
      -- the two slots of a binary rule carry the two nonterminals'
      -- meanings; matching on the ARITY, never on a term
      slotX : QNT → QNT → Bool → Type₀
      slotX Q' T true  = Val Q'
      slotX Q' T false = Val T

      branch : (r : C.Rule P) → C.G.⟦ C.ruleF P r ⟧c Mot ⊢ Δ (Val P)
      branch (inl (e , pf))      = pureA (Val P) (unitVal P e pf)
      branch (inr (Q' , T , pf)) =
        mapA (λ f → binVal P Q' T pf (f true) (f false))
             (⊗A appop {A = λ a → C.G.⟦ C.binSlot Q' T a ⟧c Mot} (slotX Q' T)
                 (λ { true  → &ᴰA Bool true idA
                    ; false → &ᴰA Bool true idA }))

  -- THE INTERPRETER: a parse tree, run.
  interp : (P : QNT) → C.Deriv P ⊢ Δ (Val P)
  interp = AI.recA alg

  -- THE PIPELINE, still a term. `mapR` applies the interpreter on the
  -- success branch and leaves the refutation alone, so `outD` is `⊤G ⊢
  -- Result (¬G C.Deriv P) (Δ (Val P))` and nothing has been externalised.

  outD : (P : QNT) → ⊤G ⊢ Result (¬G C.Deriv P) (Δ (Val P))
  outD P = mapR (¬G C.Deriv P) (Δ (Val P)) (interp P) ∘g CD.derives? P

  derives! : (P : QNT) → ⊤G ⊢ Δ Bool
  derives! P = okA (C.Deriv P) (¬G C.Deriv P) ∘g CD.derives? P

  -- the only externalisations, and they belong in `refl` lines
  runOut : (P : QNT) → Word → Maybe (Val P)
  runOut P = runΔ (Val P) (¬G C.Deriv P) (outD P)

  -- §4 THE PRINTED TRACE, AS A GRAMMAR. The output is a pair of concurrent
  -- streams, which IS a trace given by its projections.

  Prints : Wd × Wd → Gr
  Prints p = ⌈ p .fst ⌉ ⊗' ⌈ p .snd ⌉

  private
    module TrR = DecRep (Fibered.carrier trFib)

  open DE.DecEnum trFib using (dec-⊗-cuts)

  litW : (u : Word) → Probe ⌈ u ⌉
  litW u = TrR.dec-⌈⌉ discreteWord u

  -- PRIMITIVE (phase 1): the search over shuffles.  One splitting at a
  -- time, both slots compared to a literal.
  probe-Prints : (p : Wd × Wd) → Probe (Prints p)
  probe-Prints (u , v) m _ =
    dec-⊗-cuts appop (λ b → if b then ⌈ u ⌉ else ⌈ v ⌉) m
      (shuffles m) (enumComplete appop m)
      (λ sp → decΠBool
                {B = λ b → (if b then ⌈ u ⌉ else ⌈ v ⌉) (MonParts appop m sp b)}
                (litW u (MonParts appop m sp true)  tt)
                (litW v (MonParts appop m sp false) tt))

  prints! : (p : Wd × Wd) → ⊤G ⊢ Δ Bool
  prints! p = okA (Prints p) (¬G Prints p) ∘g probe-Prints p

  -- §5 THE QUINE EQUATION, stated in the calculus.

  selfDeriv : (w : Word) → run (derives! ntS) w ≡ true → C.Deriv ntS w
  selfDeriv = witness (C.Deriv ntS) (¬G C.Deriv ntS) (CD.derives? ntS)

  selfLit : (w : Word) → run (derives! ntS) w ≡ true → ⌈ w ⌉ ⊢ C.Deriv ntS
  selfLit w pf = ⌈⌉-E (selfDeriv w pf)

  -- WHAT `w` PRINTS: the two concurrent streams, read off the parse.
  printed : (w : Word) → run (derives! ntS) w ≡ true → Wd × Wd
  printed w pf = (interp ntS ∘g selfLit w pf) w (⌈⌉-pt w) .fst

  IsQuine : (w : Word) → run (derives! ntS) w ≡ true → Type₀
  IsQuine w pf = Prints (printed w pf) w

  -- ... and both answers are CONTENT, not observations: the error
  -- grammar of `probe-Prints` is `¬G _`, so a negative one says no
  -- interleaving of the printed streams is `w`.
  quineAt : (w : Word) (pf : run (derives! ntS) w ≡ true)
          → run (prints! (printed w pf)) w ≡ true → IsQuine w pf
  quineAt w pf = witness (Prints (printed w pf)) (¬G Prints (printed w pf))
                         (probe-Prints (printed w pf)) w

  notQuineAt : (w : Word) (pf : run (derives! ntS) w ≡ true)
             → run (prints! (printed w pf)) w ≡ false
             → (¬G Prints (printed w pf)) w
  notQuineAt w pf = refute (Prints (printed w pf)) (¬G Prints (printed w pf))
                           (probe-Prints (printed w pf)) w

  -- a rejected log is a REFUTATION: no parse tree exists, at this
  -- independence relation
  noDeriv : (w : Word) → run (derives! ntS) w ≡ false → (¬G C.Deriv ntS) w
  noDeriv = refute (C.Deriv ntS) (¬G C.Deriv ntS) (CD.derives? ntS)

-- THE TWO INSTANTIATIONS.  `Conc` is THE concurrent quine and is
-- re-exported unqualified; `Full` is the ⊤-endpoint control, where
-- every pair of events commutes and the hash may drift past the code.

module Conc = Over Ind decInd isPropInd
module Full = Over ⊤I  dec⊤I  isProp⊤I

open Conc public
