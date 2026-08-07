{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A CONCURRENT QUINE -- the quine, in the theory of TRACES.

  `Quine.Base` is a quine over STRINGS: one program, one word, and the
  output is a word.  Here the program is emitted by TWO CONCURRENT
  SESSIONS and the log is a TRACE -- an equivalence class of words under
  commuting independent events -- so both halves of "this text prints
  itself" have to be re-read, and the re-reading is the content.

  ==================================================================
  §A  WHAT IS CONCURRENT ABOUT IT.

  The alphabet is `Instances.Traces.Protocol`'s, reused UNCHANGED: an
  event is a session id and an action, and

      Ind (i , a) (j , b)  =  i ≠ j

  -- different sessions commute, a session with itself does not.  The
  five letters this file uses are

      a0 = (s₀ , opn)   code bit 0        b0 = (s₁ , opn)   data bit 0
      a1 = (s₀ , msg)   code bit 1        b1 = (s₁ , msg)   data bit 1
      hsh= (s₀ , cls)   the hash                (s₁ , cls)  unused

  so SESSION 0 CARRIES THE CODE AND THE HASH and SESSION 1 CARRIES THE
  DATA.  A program is still `code # data`, but the three pieces are no
  longer laid end to end: the data is INDEPENDENT of both the code and
  the hash, so it floats freely through them and

      a0 hsh b0 b0    a0 b0 hsh b0    a0 b0 b0 hsh
      b0 a0 hsh b0    b0 a0 b0 hsh    b0 b0 a0 hsh

  are SIX SPELLINGS OF ONE TRACE.  What the code and the hash still fix
  is their own relative order -- they are the same session, hence
  dependent -- and that is the one ordering constraint the whole
  construction turns on (§D).

  WHO PRINTS WHAT.  The interpreter's output is not a word.  It is a
  PAIR of words, one per session:

      session 0 prints   dec(data) ++ "#"     -- the code, and the hash
      session 1 prints   enc(dec(data))       -- the quoted code

  Each session's text is a function of the OTHER's: session 0's code is
  read off session 1's data, and session 1's data is the quote of
  session 0's code.  The fixed point is MUTUAL, which is what makes this
  a concurrent quine rather than two quines side by side.

  ==================================================================
  §B  THE QUINE EQUATION IS AN EQUATION OF TRACES.

  A pair of concurrent streams IS a trace, presented by its projections,
  and the words that trace can be spelled as are exactly

      Prints (u , v)  =  ⌈ u ⌉ ⊗' ⌈ v ⌉

  -- `⊗'` at this promodel is I-shuffling, so `Prints p w` says "w is
  one interleaving of the two streams".  So

      IsQuine w  =  Prints (what w prints) w

  and this is genuinely weaker than word equality: it is satisfied by
  every spelling of the printed trace at once.  `TraceTests` exhibits a
  quine and then checks all SIX of its spellings, with one `refl` each,
  and checks that the OUTPUT is the same pair for all six -- the
  interpreter cannot see the interleaving, which is the theorem that
  makes the trace reading legitimate.

  ==================================================================
  §C  THE GRAMMAR.  `Quine.Base`'s, with one nonterminal added because
  the code bits and the data bits are now different letters.

      S → B R            a program: the opcode, then the rest
      R → B R | H E      more code, or the hash and the data
      H → 'hsh'
      B → 'a0' | 'a1'    a CODE bit          (session 0)
      E → D O            the data: a bit, then …
      O → 'b0' | 'b1'    … the pair's second bit, ending the data
        | D E            … or the second bit and more data
      D → 'b0' | 'b1'    a DATA bit          (session 1)

  ONE `⊗'`, TWO READINGS, decided by the alphabet and not by the
  grammar.  In `S → B ⊗' R` and `R → B ⊗' R` the left slot is a session-0
  letter and the right slot still owes session-0 letters, so no `right`
  step is licensed and `⊗'` is CONCATENATION: the code bits precede the
  hash.  In `R → H ⊗' E` the left slot is session 0 and the right slot is
  entirely session 1, so `⊗'` is FULL INTERLEAVING: the data may appear
  anywhere.  This is exactly `Protocol`'s observation, and §D is the
  measurement of it.

  THE INTERPRETER.  As in `Quine.Base`, only the DATA is read -- the
  decoding `dec` is the grammar's own pairing (`E → D O`, `O → D E`),
  one projection per node, and never a function on words.  The first
  code bit is the OPCODE, and it chooses the one order still left to
  choose:

      opcode 0 :  session 0 prints   dec(e) ++ "#"
      opcode 1 :  session 0 prints   "#" ++ dec(e)

  and session 1 prints `enc(dec(e))` either way.  Over strings the
  opcode chose between "code then data" and "data then code"; here that
  choice HAS BEEN TAKEN AWAY BY THE ALPHABET, because the code and the
  data are concurrent and the two orders are the same trace.  What
  survives is the code/hash order, which is still recorded because they
  share a session.

  A source is a quine at opcode 0 exactly when the session-0 word is
  `dec(data) ++ #` and the session-1 word is `enc(dec(data))`; the
  shortest is `a0 hsh ∥ b0 b0`, four events.  At opcode 1 it is a quine
  exactly when the session-0 word is `# ++ dec(data)` -- WHICH THE
  GRAMMAR FORBIDS AT `Ind`, because the hash and the code bits are the
  same session.

  ==================================================================
  §D  THE CONTROLLED EXPERIMENT, and the actual research finding.

  `Over` is parameterised by the independence relation, exactly as
  `Protocol.Over` is, and is instantiated twice:

      Conc = Over Ind …    events of different sessions commute
      Full = Over ⊤I  …    EVERYTHING commutes

  Same grammar, same interpreter, same decision procedure; one
  `Fibered`.  And the answer differs, in the strongest way available:

      hsh a1 b1 b1        IS A QUINE at ⊤I
                          IS NOT EVEN A PROGRAM at Ind

  At `⊤I` the hash may commute past the code bit, so `S → B ⊗' R` can
  take the opcode `a1` from the SECOND position; the parse then reads
  opcode 1 and data `b1 b1`, decodes `[1]`, and prints
  `("#" ++ "1" , "11")` -- itself.  At `Ind` that commutation is
  forbidden, `S` has no derivation at all, and `TraceTests` proves it
  (the error grammar is `¬G _`, so the negative answer is a refutation
  and not a report).

  So the independence relation is doing real work on the QUINE
  PREDICATE and not merely on the language.  That is the trace analogue
  of `ProtocolTests.Control.wrong-at-⊤`, one level up: there the ⊤
  endpoint certified a log that violates the protocol, here it
  certifies a SELF-PRINTING PROGRAM that does not exist.

  THE CONVERSE SEPARATION DOES NOT EXIST, and the argument is short
  enough to state.  `ITr Ind ⊆ ITr ⊤I` -- the side condition on `right`
  only weakens -- so every `Ind`-parse tree is a `⊤I`-parse tree, with
  the same value.  Hence if some `Ind`-derivation of `w` prints `w`,
  some `⊤I`-derivation does too: `⊤I` has strictly MORE quines, never
  fewer.  (What that argument does not settle is which parse the
  DECISION PROCEDURE happens to find first at `⊤I`, since `printed`
  reads the found one; `TraceTests.Control.still-a-quine` exhibits the
  four-event quine surviving that, by evaluation.)

  A NEGATIVE RESULT WORTH RECORDING, because it was the first design
  tried and it fails.  Put the code in session 0 and the data in session
  1 with NO hash -- the session already separates them -- and the quine
  set does not depend on `I` at all.  The reason: session 1's printed
  stream is `enc(d)` and the equation forces it to be the source's own
  session-1 word, so `d` is pinned to the canonical decoding no matter
  how freely the parse may re-pair the data, and then session 0's word
  is pinned too.  A self-referential equation is rigid enough to undo
  the extra freedom.  The hash is what breaks the symmetry: it is a
  session-0 letter whose POSITION relative to the code is recorded by
  `Ind` and forgotten by `⊤I`, and the opcode makes the output depend
  on that position.  So the separation needs BOTH a same-session
  ordering constraint and an instruction that can print in the
  constrained order -- neither alone is enough.

  ==================================================================
  DEFINES the alphabet aliases, the grammar `QNT`/`qunitR`/`qbinR`, the
  interpreter (`Val`/`unitVal`/`binVal`/`emit`), and -- inside `module
  Over`, parameterised by the independence relation -- the CYK
  instantiation, the decision `derives?`, the interpreter as a term
  `interp`, the printed-trace grammar `Prints` with its probe, and the
  quine equation `IsQuine` with the two ways to discharge it.
-}
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

-- ==================================================================
-- §0  THE ALPHABET, REUSED.
--
-- `Protocol`'s two sessions and three actions, read as the tiny quine
-- language's letters.  Nothing about the alphabet is new -- the
-- independence relation, its decidability and its propositionality all
-- come from `Protocol` -- which is what makes `Conc`/`Full` below the
-- SAME experiment run at two promodels.
-- ==================================================================

Wd : Type₀
Wd = List Ev

a0 a1 hsh b0 b1 : Ev
a0  = s₀ , opn        -- code bit 0, session 0
a1  = s₀ , msg        -- code bit 1, session 0
hsh = s₀ , cls        -- the hash,   session 0
b0  = s₁ , opn        -- data bit 0, session 1
b1  = s₁ , msg        -- data bit 1, session 1

-- ==================================================================
-- §1  THE GRAMMAR.
--
-- `Quine.Base`'s, plus `D` -- over strings the code and the data were
-- the same two letters and `#` told them apart; here the SESSION tells
-- them apart, so the two bit classes are two nonterminals and the hash
-- has become an ordering marker rather than a separator.
-- ==================================================================

data QNT : Type₀ where ntS ntR ntH ntB ntE ntO ntD : QNT

-- The terminal productions.  Stated as `Eq`-equations (`Protocol`'s
-- idiom) rather than as a type family on letters: matching `Eq.refl`
-- determines the letter, which is what makes `qallComplete` twenty
-- lines instead of ninety.
qunitR : QNT → Ev → Type₀
qunitR ntS e = ⊥
qunitR ntR e = ⊥
qunitR ntE e = ⊥
qunitR ntH e = e Eq.≡ hsh
qunitR ntB e = (e Eq.≡ a0) ⊎ (e Eq.≡ a1)
qunitR ntO e = (e Eq.≡ b0) ⊎ (e Eq.≡ b1)
qunitR ntD e = (e Eq.≡ b0) ⊎ (e Eq.≡ b1)

-- The binary productions, indexed: `BinIx P` says HOW MANY a
-- nonterminal has and `blhs`/`brhs` name the two children.  `R` is the
-- only nonterminal with two, so the index is `Bool` there and `Unit`
-- elsewhere.  Again `Protocol`'s idiom, generalised by one bit.
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

-- ==================================================================
-- §2  THE INTERPRETER, as a semantic action.
--
-- One meaning per nonterminal, one metalanguage combination per
-- production -- which is what a `Δ`-valued algebra IS.  Nothing here
-- looks at a word: `dec` never appears, because the pairing that
-- realises it is the grammar's own structure.
--
--     B ↦ the code bit            E ↦ dec of the data below it
--     D ↦ the data bit            O ↦ dec of the data below it
--     H ↦ nothing                 R ↦ dec of the data
--                                 S ↦ THE OUTPUT, a pair of streams
-- ==================================================================

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

-- THE OPCODE'S MEANING.  `emit b d` is the PAIR of streams a program
-- with opcode `b` and decoded data `d` prints.  Session 1's stream does
-- not depend on the opcode -- and it could not, because the only order
-- an opcode can still choose is one the alphabet still records, and the
-- alphabet no longer records "code before data".
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

-- ==================================================================
-- §3  EVERYTHING ELSE, OVER AN ARBITRARY INDEPENDENCE RELATION.
--
-- The grammar and the interpreter above mention no splitting, so they
-- are shared.  What follows -- CYK, the decision, the printed-trace
-- grammar, the quine equation -- depends on the alphabet's independence
-- relation only through `Traces/Base`'s `Split`, so it is a module in
-- that relation and the file ends by instantiating it twice.
--
-- `Protocol.Over` is opened wholesale: the trace promodel, the grading
-- `trGraded`, the resource probe `probe-NT`, `module CYK` and its
-- `Decide`, `litProbe` and `discreteWord` are REUSED, not one token
-- changed.  Everything of `Protocol`'s that is about the PROTOCOL
-- (`NT`, `Deriv`, `derives?`, …) is in scope too and simply never
-- named; this file's own CYK lives behind `C`.
-- ==================================================================

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

  -- ================================================================
  -- The interpreter, as a term.  `Quine.Base.Interp` verbatim, with
  -- `strFib` replaced by `trFib` and the grammar replaced by this one.
  -- ================================================================

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

  -- ================================================================
  -- THE PIPELINE, still a term.  `mapR` applies the interpreter on the
  -- success branch and leaves the refutation alone, so `outD` is
  -- `⊤G ⊢ Result (¬G C.Deriv P) (Δ (Val P))` and nothing has been
  -- externalised.
  -- ================================================================

  outD : (P : QNT) → ⊤G ⊢ Result (¬G C.Deriv P) (Δ (Val P))
  outD P = mapR (¬G C.Deriv P) (Δ (Val P)) (interp P) ∘g CD.derives? P

  derives! : (P : QNT) → ⊤G ⊢ Δ Bool
  derives! P = okA (C.Deriv P) (¬G C.Deriv P) ∘g CD.derives? P

  -- the only externalisations, and they belong in `refl` lines
  runOut : (P : QNT) → Word → Maybe (Val P)
  runOut P = runΔ (Val P) (¬G C.Deriv P) (outD P)

  -- ================================================================
  -- §4  THE PRINTED TRACE, AS A GRAMMAR.
  --
  -- The output is a pair of concurrent streams, which IS a trace given
  -- by its projections.  `Prints (u , v)` is the grammar of the words
  -- that trace can be spelled as -- `⊗'` here is I-shuffling, so this
  -- says "one interleaving of what session 0 printed with what session
  -- 1 printed", and NOTHING about which one.
  --
  -- It is decided by the enumeration of shuffles plus word equality:
  -- `dec-⊗-cuts` is the same combinator `decBin` uses, at the two
  -- representables instead of at two chart entries.
  -- ================================================================

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

  -- ================================================================
  -- §5  THE QUINE EQUATION, stated in the calculus.
  --
  -- `witness` EXTRACTS the parse tree from the decision -- the tree is a
  -- theorem, not a report -- and `⌈_⌉` PINS it to the source: `⌈ w ⌉`
  -- holds at one world and that world IS the source, so
  --
  --     ⌈ w ⌉  --selfLit-->  C.Deriv S  --interp-->  Δ (Wd × Wd)
  --
  -- is "the log at `w`, parsed and run", and by `⌈⌉-UP` it is just a
  -- pair of words, read off at the point `⌈⌉-pt w = Eq.refl`.
  --
  -- `IsQuine` then says that pair, read as a TRACE, has `w` among its
  -- spellings.  Over strings the corresponding statement is an equation
  -- between two words; here it is a `⊗'`, and the difference is exactly
  -- the six spellings `TraceTests` checks.
  -- ================================================================

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

-- ==================================================================
-- THE TWO INSTANTIATIONS.  `Conc` is THE concurrent quine and is
-- re-exported unqualified; `Full` is the ⊤-endpoint control, where
-- every pair of events commutes and the hash may drift past the code.
-- ==================================================================

module Conc = Over Ind decInd isPropInd
module Full = Over ⊤I  dec⊤I  isProp⊤I

open Conc public
