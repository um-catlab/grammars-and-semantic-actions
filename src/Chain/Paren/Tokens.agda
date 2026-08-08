{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  A REAL SURFACE SYNTAX FOR LINEAR STLC: ARBITRARY NAMES, SHADOWING,
  PARENTHESES, AND TYPE ANNOTATIONS.

  `Lambda.Parse`'s alphabet was four tokens -- `x y λx. λy.` -- with two
  variable names, application by bare juxtaposition, and no type syntax.
  Three separate results in this development trace back to that:

    -- the grammar is AMBIGUOUS (`Chain.Pipeline` §4), so the CYK chart
       must try every cut;
    -- `Chain.PrintTests.notInjective` REFUTES `Section` for the printer;
    -- the reprint of the chain's own term does not decide in seven
       minutes (measured).

  This alphabet fixes all three at the source, and adds what
  `Chain.Rust` needed and could not have: annotations.

  ==================================================================
  THE TOKENS.

      tid n         an identifier -- ANY name, `Name = List Char`
      tlam  tdot    `\`  `.`
      tlp   trp     `(`  `)`
      tcolon        `:`
      tarrow        `-o`
      tbase         `o`          the base type

  `o` IS A KEYWORD, so no variable may be called `o`.  That is the one
  restriction on names and it is the usual one; everything else
  alphabetic is an identifier.  A binder is now THREE tokens (`\`, the
  name, `.`) rather than one, which is what makes arbitrary names
  possible -- `Chain.Lex` could hard-code `λx.` precisely because there
  were only two of them.

  ==================================================================
  THE GRAMMAR THIS IS FOR -- fully parenthesised, so unambiguous:

      trm ::=  id
            |  \ id . trm
            |  ( trm trm )
            |  ( trm : ty )
      ty  ::=  o
            |  ( ty -o ty )

  APPLICATION IS PARENTHESISED, which is not merely a convenience.  It
  means EVERY recursive occurrence is preceded by a literal token, so a
  sub-derivation's word is strictly shorter than the whole -- and that
  is exactly `Decidable.Inductive`'s guardedness obligation, discharged
  by the shape of the grammar rather than by a lemma about FIRST sets.
  A spine grammar (`trm ::= atom rest`) would put a recursive occurrence
  at the START of a production and lose it.

  SHADOWING is a fact about SCOPE RESOLUTION, not about this file: the
  parser produces a NAMED tree and `Chain.Paren.Elab` resolves names
  innermost-first, so `\x. \x. x` binds the inner one.

  PHASE.  All of it is phase 1 -- a scanner and its alphabet, marked as
  `Chain.Aligned` §1 is.  The PARSER is the thing that must live in the
  calculus, and it does: `Chain.Paren.Grammar` is a `μ` decided by
  `Decidable.Inductive.decμ`.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Tokens where

open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
import Cubical.Data.Equality as Eq

open import Agda.Builtin.Char using (Char; primCharEquality; primCharToNat)
open import Agda.Builtin.Char.Properties using (primCharToNatInjective)
open import Agda.Builtin.String using (primStringToList) renaming (String to UString)

open import TheoryGrammar.Enumerable using (No)

-- ==================================================================
-- §1  NAMES, AND DECIDABLE EQUALITY WITHOUT A POSTULATE.
--
-- `Chain.Lex`'s construction, reused: `primCharToNatInjective` is an
-- Agda primitive, so `Char` embeds in `ℕ` and equality is `ℕ`'s pulled
-- back.  Nothing here postulates anything.
-- ==================================================================

Name : Type₀
Name = List Char

decℕ : (a b : ℕ) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decℕ zero    zero    = inl Eq.refl
decℕ zero    (suc _) = inr λ ()
decℕ (suc _) zero    = inr λ ()
decℕ (suc a) (suc b) with decℕ a b
... | inl p = inl (Eq.ap suc p)
... | inr k = inr λ { Eq.refl → k Eq.refl }

decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decChar a b with decℕ (primCharToNat a) (primCharToNat b)
... | inl p = inl (primCharToNatInjective a b p)
... | inr k = inr λ { Eq.refl → k Eq.refl }

decName : (a b : Name) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decName []      []      = inl Eq.refl
decName []      (_ ∷ _) = inr λ ()
decName (_ ∷ _) []      = inr λ ()
decName (c ∷ a) (d ∷ b) = both (decChar c d) (decName a b)
  where both : _ → _ → (((c ∷ a)) Eq.≡ (d ∷ b)) ⊎ No ((c ∷ a) Eq.≡ (d ∷ b))
        both (inl Eq.refl) (inl Eq.refl) = inl Eq.refl
        both (inr k)       _             = inr λ { Eq.refl → k Eq.refl }
        both _             (inr k)       = inr λ { Eq.refl → k Eq.refl }

-- ==================================================================
-- §2  THE TOKENS.
-- ==================================================================

data Tok : Type₀ where
  tid     : Name → Tok
  tlam    : Tok            -- \
  tdot    : Tok            -- .
  tlp     : Tok            -- (
  trp     : Tok            -- )
  tcolon  : Tok            -- :
  tarrow  : Tok            -- -o
  tbase   : Tok            -- o

-- PRIMITIVE (phase 1): decidable equality.  The parser's constants are
-- token literals, so this is what decides every one of them.
decTok : (a b : Tok) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decTok (tid m) (tid n) with decName m n
... | inl Eq.refl = inl Eq.refl
... | inr k       = inr λ { Eq.refl → k Eq.refl }
decTok tlam   tlam   = inl Eq.refl
decTok tdot   tdot   = inl Eq.refl
decTok tlp    tlp    = inl Eq.refl
decTok trp    trp    = inl Eq.refl
decTok tcolon tcolon = inl Eq.refl
decTok tarrow tarrow = inl Eq.refl
decTok tbase  tbase  = inl Eq.refl
decTok (tid _) tlam   = inr λ () ; decTok (tid _) tdot   = inr λ ()
decTok (tid _) tlp    = inr λ () ; decTok (tid _) trp    = inr λ ()
decTok (tid _) tcolon = inr λ () ; decTok (tid _) tarrow = inr λ ()
decTok (tid _) tbase  = inr λ ()
decTok tlam (tid _) = inr λ () ; decTok tlam tdot   = inr λ ()
decTok tlam tlp     = inr λ () ; decTok tlam trp    = inr λ ()
decTok tlam tcolon  = inr λ () ; decTok tlam tarrow = inr λ ()
decTok tlam tbase   = inr λ ()
decTok tdot (tid _) = inr λ () ; decTok tdot tlam   = inr λ ()
decTok tdot tlp     = inr λ () ; decTok tdot trp    = inr λ ()
decTok tdot tcolon  = inr λ () ; decTok tdot tarrow = inr λ ()
decTok tdot tbase   = inr λ ()
decTok tlp (tid _) = inr λ () ; decTok tlp tlam   = inr λ ()
decTok tlp tdot    = inr λ () ; decTok tlp trp    = inr λ ()
decTok tlp tcolon  = inr λ () ; decTok tlp tarrow = inr λ ()
decTok tlp tbase   = inr λ ()
decTok trp (tid _) = inr λ () ; decTok trp tlam   = inr λ ()
decTok trp tdot    = inr λ () ; decTok trp tlp    = inr λ ()
decTok trp tcolon  = inr λ () ; decTok trp tarrow = inr λ ()
decTok trp tbase   = inr λ ()
decTok tcolon (tid _) = inr λ () ; decTok tcolon tlam   = inr λ ()
decTok tcolon tdot    = inr λ () ; decTok tcolon tlp    = inr λ ()
decTok tcolon trp     = inr λ () ; decTok tcolon tarrow = inr λ ()
decTok tcolon tbase   = inr λ ()
decTok tarrow (tid _) = inr λ () ; decTok tarrow tlam   = inr λ ()
decTok tarrow tdot    = inr λ () ; decTok tarrow tlp    = inr λ ()
decTok tarrow trp     = inr λ () ; decTok tarrow tcolon = inr λ ()
decTok tarrow tbase   = inr λ ()
decTok tbase (tid _) = inr λ () ; decTok tbase tlam   = inr λ ()
decTok tbase tdot    = inr λ () ; decTok tbase tlp    = inr λ ()
decTok tbase trp     = inr λ () ; decTok tbase tcolon = inr λ ()
decTok tbase tarrow  = inr λ ()

-- ==================================================================
-- §3  THE SCANNER.  PRIMITIVE (phase 1) throughout.
--
-- Identifiers are maximal alphabetic runs, so the scanner accumulates
-- rather than emitting per character -- which is exactly why
-- `Chain.Lex`'s five-state table could not do this and why `λx.` had to
-- be one token there.
-- ==================================================================

private
  _=c_ : Char → Char → Bool
  _=c_ = primCharEquality

-- is this character part of an identifier?  Letters only, and the
-- alphabet is listed rather than ranged so the test computes.
isAlpha : Char → Bool
isAlpha c = go ('a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷ 'g' ∷ 'h' ∷ 'i' ∷ 'j'
              ∷ 'k' ∷ 'l' ∷ 'm' ∷ 'n' ∷ 'o' ∷ 'p' ∷ 'q' ∷ 'r' ∷ 's' ∷ 't'
              ∷ 'u' ∷ 'v' ∷ 'w' ∷ 'x' ∷ 'y' ∷ 'z' ∷ [])
  where go : List Char → Bool
        go []       = false
        go (d ∷ ds) = if c =c d then true else go ds

isSpace : Char → Bool
isSpace c = if c =c ' ' then true else (if c =c '\n' then true else false)

-- `o` is the base type, not a name
keyword : Name → Tok
keyword n = if isBase n then tbase else tid n
  where isBase : Name → Bool
        isBase ('o' ∷ []) = true
        isBase _          = false

-- PRIMITIVE (phase 1): peel a maximal alphabetic run.
ident : List Char → Name × List Char
ident []       = [] , []
ident (c ∷ cs) = if isAlpha c then cons c (ident cs) else ([] , c ∷ cs)
  where cons : Char → Name × List Char → Name × List Char
        cons d nr = (d ∷ nr .fst) , nr .snd

-- PRIMITIVE (phase 1): the scanner.  `nothing` is a LEXICAL error: a
-- character no token begins with.  Fuel is the character count, which
-- always decreases, so the recursion is structural in disguise.
scan : ℕ → List Char → Maybe (List Tok)
scan _       []       = just []
scan zero    _        = nothing
scan (suc k) (c ∷ cs) =
  if isSpace c then scan k cs
  else (if c =c '(' then push tlp    (scan k cs)
  else (if c =c ')' then push trp    (scan k cs)
  else (if c =c '.' then push tdot   (scan k cs)
  else (if c =c ':' then push tcolon (scan k cs)
  else (if c =c '\\' then push tlam  (scan k cs)
  else (if c =c 'λ'  then push tlam  (scan k cs)
  else (if c =c '-'  then arrow cs
  else (if isAlpha c then idRun (c ∷ cs) else nothing))))))))
  where
  push : Tok → Maybe (List Tok) → Maybe (List Tok)
  push t (just ts) = just (t ∷ ts)
  push t nothing   = nothing

  arrow : List Char → Maybe (List Tok)
  arrow (d ∷ ds) = if d =c 'o' then push tarrow (scan k ds) else nothing
  arrow []       = nothing

  idRun : List Char → Maybe (List Tok)
  idRun ds = go (ident ds)
    where go : Name × List Char → Maybe (List Tok)
          go (n , rest) = push (keyword n) (scan k rest)

lexS : UString → Maybe (List Tok)
lexS s = go (primStringToList s)
  where go : List Char → Maybe (List Tok)
        go cs = scan (len cs) cs
          where len : List Char → ℕ
                len []       = 0
                len (_ ∷ ds) = suc (len ds)

-- ==================================================================
-- §4  IT SCANS.  Arbitrary names, shadowing, annotations.
-- ==================================================================

nx ny nfoo : Name
nx   = 'x' ∷ []
ny   = 'y' ∷ []
nfoo = 'f' ∷ 'o' ∷ 'o' ∷ []

-- a long name, and a SHADOWING binder -- both impossible before
_ : lexS "\\foo. foo"
  ≡ just (tlam ∷ tid nfoo ∷ tdot ∷ tid nfoo ∷ [])
_ = refl

_ : lexS "\\x. \\x. x"
  ≡ just (tlam ∷ tid nx ∷ tdot ∷ tlam ∷ tid nx ∷ tdot ∷ tid nx ∷ [])
_ = refl

-- the identity, annotated
_ : lexS "((\\x. x) : (o -o o))"
  ≡ just (tlp ∷ tlp ∷ tlam ∷ tid nx ∷ tdot ∷ tid nx ∷ trp
        ∷ tcolon ∷ tlp ∷ tbase ∷ tarrow ∷ tbase ∷ trp ∷ trp ∷ [])
_ = refl

-- application is PARENTHESISED, so these are different token streams --
-- the ambiguity that forced the CYK chart is gone at the source
_ : lexS "((\\x. x) (\\y. y))"
  ≡ just (tlp ∷ tlp ∷ tlam ∷ tid nx ∷ tdot ∷ tid nx ∷ trp
        ∷ tlp ∷ tlam ∷ tid ny ∷ tdot ∷ tid ny ∷ trp ∷ trp ∷ [])
_ = refl

_ : lexS "(\\x. (x (\\y. y)))"
  ≡ just (tlp ∷ tlam ∷ tid nx ∷ tdot ∷ tlp ∷ tid nx
        ∷ tlp ∷ tlam ∷ tid ny ∷ tdot ∷ tid ny ∷ trp ∷ trp ∷ trp ∷ [])
_ = refl

-- `λ` is accepted as well as `\`
_ : lexS "λx. x" ≡ lexS "\\x. x"
_ = refl

-- `o` is a KEYWORD: it lexes as the base type, not as a name
_ : lexS "o" ≡ just (tbase ∷ [])
_ = refl

_ : lexS "oo" ≡ just (tid ('o' ∷ 'o' ∷ []) ∷ [])
_ = refl

-- lexical errors
_ : lexS "x @ y" ≡ nothing
_ = refl

_ : lexS "o - o" ≡ nothing            -- `-` alone is not a token; `-o` is
_ = refl
