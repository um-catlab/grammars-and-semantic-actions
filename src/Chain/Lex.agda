{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  STAGE 1 OF THE CHAIN: UNICODE CHARACTERS -> TOKENS.

  THE THEORY IS INSTANTIATED AT THE UNICODE MONOID.  `Strings.Base` is a
  module in an ARBITRARY alphabet,

      module TheoryGrammar.Instances.Strings.Base (Char : Type₀)

  and this file applies it at Agda's primitive `Char`, i.e. at the free
  monoid on Unicode scalars.  `Chain.Parse` applies the SAME module at
  the token type.  Nothing is redefined between the two; that reuse is
  the whole point of the exercise, and it is a module application.

  ------------------------------------------------------------------
  THE LEXER IS AN ALGEBRA, NOT A LOOP.

  `Strings.Automata` already supplies the three pieces `runAut` wants at
  this theory:

      ScanF      = starF char        the functor "read one char, or stop"
      scanCoalg  : Scanner ScanF     ⊤'s own decomposition
      scanLC     : LocallyContractive ScanF

  and its `DFA` module builds ONE algebra for that functor -- the
  acceptance predicate `Q → Bool`.  This file builds a SECOND one, at
  carrier

      Q → Maybe (List LTok)

  which is the same machine reading with output.  That is the content of
  `Automata`'s header claim that "an automaton IS an algebra": swapping
  `Bool` for `Maybe (List LTok)` changes the algebra and nothing else --
  same functor, same coalgebra, same `runAut`.  A transducer is not a
  new notion here, it is a new carrier.

  The `Maybe` is the ERROR GRAMMAR of this stage, in the sense of the
  repository's `Result` discipline: `nothing` says "the scan ended in a
  state that is not a token boundary".  It propagates for free, because
  the error state `serr` is absorbing and its `fin` is `nothing`, so a
  single `Mb.map` in the character branch carries a failure all the way
  out.

  ------------------------------------------------------------------
  RETENTION: EVERY TOKEN CARRIES ITS SOURCE OFFSET.

  The output is `List LTok` with `LTok = Tok × ℕ`, the second component
  being the index IN THE CHARACTER STRING at which the token starts.
  This is the data that makes stage 5's backward projection possible,
  and it costs nothing: the offset is threaded through the automaton's
  STATE, so `runAut` computes it on the way in and the algebra never
  measures a string.

  Note the `λx.` case in particular.  The token is emitted when the `.`
  is read, but tagged with the offset of the `λ` -- which the state
  `sLx n` is carrying precisely so that the emission can be located at
  its own beginning rather than at its end.  `Lambda.Parse`'s decision
  to make `λx.` ONE token (three characters) is what forces this, and it
  is the smallest honest instance of "a token spans several characters,
  so a token index is not a character index".

  ------------------------------------------------------------------
  WHERE THE UNICODE ACTUALLY ENTERS, and why there are no postulates.

  Two places, and they are different.

  (1) `decChar`, the propositional decidability `Strings.Automata` asks
      for.  It is built from `primCharToNatInjective`, an Agda PRIMITIVE
      -- so this file needs no oracle.  `String.Unicode`'s
      `DiscreteUnicodeChar` postulates the same fact from
      `primCharEquality`; going through `primCharToNat` avoids that, at
      the cost of nothing.

  (2) `stepC` / `emitC`, the transition table.  These compare characters
      with `primCharEquality`, at `Bool`, and that is deliberate: the
      table is PHASE-1 primitive code, it is the hot path, and a
      Bool-valued comparison of two primitive characters is a machine
      instruction where a propositional one is a proof term.  The type
      of the table mentions no equality at all, so nothing downstream
      learns which comparison was used.
-}
open import Cubical.Foundations.Prelude

module Chain.Lex where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_; length; map)
open import Cubical.Data.Maybe as Mb using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using ()
import Cubical.Data.Equality as Eq

open import Agda.Builtin.Char using (Char; primCharEquality; primCharToNat)
open import Agda.Builtin.Char.Properties using (primCharToNatInjective)
open import Agda.Builtin.String using (primStringToList) renaming (String to UString)

open import TheoryGrammar.Enumerable using (No)

-- the TOKEN type is the one the parser already speaks.  `Lambda.Parse`
-- is imported for its vocabulary only -- `Tok`, `Nm`, `varTok`,
-- `lamTok` -- none of which mentions that file's fixed demo tape.
open import TheoryGrammar.Instances.Lambda.Parse using (Tok; vx; vy; lx; ly; Nm; Nx; Ny)

-- ==================================================================
-- §0  UNICODE CHARACTER EQUALITY, WITHOUT A POSTULATE.
--
-- `primCharToNatInjective` is an Agda primitive, so `Char` embeds in
-- `ℕ` and its decidable equality is `ℕ`'s pulled back along that
-- embedding.  Agda's builtin `_≡_` IS `Cubical.Data.Equality`'s `Eq.≡`
-- (the latter re-exports the former), so no transport is needed.
-- ==================================================================

decℕ : (a b : ℕ) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decℕ zero    zero    = inl Eq.refl
decℕ zero    (suc _) = inr λ ()
decℕ (suc _) zero    = inr λ ()
decℕ (suc a) (suc b) with decℕ a b
... | inl p  = inl (Eq.ap suc p)
... | inr k  = inr λ { Eq.refl → k Eq.refl }

decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decChar a b with decℕ (primCharToNat a) (primCharToNat b)
... | inl p = inl (primCharToNatInjective a b p)
... | inr k = inr λ { Eq.refl → k Eq.refl }

-- ==================================================================
-- §1  THE THEORY, AT THE UNICODE MONOID.
--
-- One module application.  `charFib` below is `strFib` at `Char`; the
-- token instantiation in `Chain.Parse` is the same line at `Tok`.
-- ==================================================================

open import TheoryGrammar.Instances.Strings.Automata Char decChar public

-- ==================================================================
-- §2  THE TOKEN STREAM, WITH OFFSETS.
-- ==================================================================

-- a token together with the CHARACTER OFFSET at which it begins
LTok : Type₀
LTok = Tok × ℕ

tokOf : LTok → Tok
tokOf = fst

atOf : LTok → ℕ
atOf = snd

-- ==================================================================
-- §3  THE TRANSITION TABLE.  PHASE 1 -- this is the primitive.
--
-- Five states.  The three `sL*` states carry the offset of the `λ` they
-- began at, which is the whole of the retention mechanism.
-- ==================================================================

data LSt : Type₀ where
  s0   : LSt          -- at a token boundary
  sL   : ℕ → LSt      -- read `λ`, which started at this offset
  sLx  : ℕ → LSt      -- read `λx`
  sLy  : ℕ → LSt      -- read `λy`
  serr : LSt          -- absorbing failure

-- the automaton's state is the lexical state paired with the CURRENT
-- character offset; threading it here is why the algebra never has to
-- measure anything
LQ : Type₀
LQ = LSt × ℕ

chλ chx chy chdot chsp : Char
chλ   = 'λ'
chx   = 'x'
chy   = 'y'
chdot = '.'
chsp  = ' '

-- PRIMITIVE (phase 1): the transition on the LEXICAL state alone.  The
-- offset half of `LQ` is not consulted here, only carried, which is why
-- it is a separate clause below.
stepS : LSt → ℕ → Char → LSt
stepS s0 i c =
  if primCharEquality c chλ   then sL i
  else (if primCharEquality c chx  then s0
  else (if primCharEquality c chy  then s0
  else (if primCharEquality c chsp then s0
  else serr)))
stepS (sL n) i c =
  if primCharEquality c chx then sLx n
  else (if primCharEquality c chy then sLy n
  else serr)
stepS (sLx n) i c = if primCharEquality c chdot then s0 else serr
stepS (sLy n) i c = if primCharEquality c chdot then s0 else serr
stepS serr    i c = serr

-- PRIMITIVE (phase 1): the transition function.  The offset ALWAYS
-- advances by one character; that is the only invariant the retention
-- data needs.
stepL : LQ → Char → LQ
stepL (s , i) c = stepS s i c , suc i

-- PRIMITIVE (phase 1): the output on each transition.  The `λx.` case
-- emits at offset `n` -- the position of the `λ` -- not at the position
-- of the `.` that triggered it.
emitL : LQ → Char → List LTok
emitL (s0 , i) c =
  if primCharEquality c chx then (vx , i) ∷ []
  else (if primCharEquality c chy then (vy , i) ∷ []
  else [])
emitL (sLx n , i) c = if primCharEquality c chdot then (lx , n) ∷ [] else []
emitL (sLy n , i) c = if primCharEquality c chdot then (ly , n) ∷ [] else []
emitL _ c = []

-- PRIMITIVE (phase 1): what the machine says at end of input.  Only a
-- token boundary is a legal place to stop, so a trailing `λx` is a
-- lexical error rather than a silently dropped prefix.
finL : LQ → Maybe (List LTok)
finL (s0 , _) = just []
finL _        = nothing

-- `Maybe`'s functorial action, spelled out rather than imported: this is
-- the one place the error grammar of this stage is propagated.
mapMb : {X Y : Type₀} → (X → Y) → Maybe X → Maybe Y
mapMb f (just x) = just (f x)
mapMb f nothing  = nothing

-- ==================================================================
-- §4  THE ALGEBRA.
--
-- Compare `Strings.Automata.DFA.dfaAlg` line for line: the ε-branch is
-- the acceptance predicate, here `finL`; the character branch is the
-- transition, here `stepL` with `emitL` prepended to the recursive
-- result.  `Mb.map` is the only addition, and it is what makes the
-- error propagate.
-- ==================================================================

Out : Fam
Out _ _ = LQ → Maybe (List LTok)

scanAlg : Algᴳ ScanF Out
scanAlg tt =
  ⊕ᴰ-E λ { true  → λ _ _ q → finL q
         ; false →
             ⊗ˢ-E appop {A = λ a → ⟦ starSlot char a ⟧c ⌞ Out ⌟}
                        {B = λ _ → LQ → Maybe (List LTok)}
                        (λ _ _ h q →
                           mapMb (emitL q (lower (h true) .fst) ++_)
                                  (h false (stepL q (lower (h true) .fst)))) }

-- the scan, as a term of the calculus at the UNICODE theory
scan : ⊤G ⊢ (λ _ → Maybe (List LTok))
scan m x = runAut scanLC scanCoalg scanAlg tt m x (s0 , 0)

-- ==================================================================
-- §5  THE ONE EXIT.  `lexS` is the only thing in the chain that takes an
-- Agda `String`; everything downstream is indexed by the character list
-- it produces.
-- ==================================================================

lexS : UString → Maybe (List LTok)
lexS s = scan (primStringToList s) tt
