{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  SOURCE TEXT TO `LinTyped.Raw`, THROUGH THE NEW FRONT END.

      String --lexS--> [Tok] --parseTrm--> Trm --toRaw--> Raw

  `lexS` is `Chain.Paren.Tokens`' scanner, `parseTrm` is
  `Chain.Paren.Grammar`'s `decμ`, and `toRaw` is `Chain.Paren.Elab`'s
  semantic action at `dbAlg`.  Only the last line of §1 leaves the
  calculus, and it leaves once.

  WHAT THIS REPLACES.  `Chain.Rust` had to start from a `Raw` written by
  hand in Agda, because `Lambda.Parse`'s alphabet was `{x, y, λx., λy.}`
  and had nowhere to put a type annotation.  It now starts from a
  string, with arbitrary names and shadowing.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Pipeline where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sum using (inl; inr)

open import Agda.Builtin.String using () renaming (String to UString)

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar
open import Chain.Paren.Elab

import TheoryGrammar.Instances.LinTyped as LT

-- ==================================================================
-- §1  THE FRONT END, COMPOSED.
-- ==================================================================

-- PRIMITIVE (phase 1): the exit.  `parseTrm ts tt` is `Dec⟨ Trm ⟩ ts`,
-- i.e. `Trm ts ⊎ ¬ Trm ts`, so the `inr` branch discards a REFUTATION
-- of the token stream's being a term -- available to a diagnostic, and
-- not needed by this composite.
elabToks : List Tok → Maybe LT.Raw
elabToks ts with parseTrm ts tt
... | inr _ = nothing
... | inl d = toRaw ts d .fst []

elab : UString → Maybe LT.Raw
elab s with lexS s
... | nothing = nothing
... | just ts = elabToks ts

-- ==================================================================
-- §2  IT RUNS.  Arbitrary names, shadowing, annotations, scope errors.
-- ==================================================================

-- ---- arbitrary names ----------------------------------------------
_ : elab "\\foo. foo" ≡ just (LT.lam (LT.var 0))
_ = refl

_ : elab "\\longname. longname" ≡ just (LT.lam (LT.var 0))
_ = refl

-- ---- SHADOWING: the inner binder wins ------------------------------
_ : elab "\\x. \\x. x" ≡ just (LT.lam (LT.lam (LT.var 0)))
_ = refl

-- ... and without shadowing the index is 1
_ : elab "\\x. \\y. x" ≡ just (LT.lam (LT.lam (LT.var 1)))
_ = refl

_ : elab "\\x. \\y. y" ≡ just (LT.lam (LT.lam (LT.var 0)))
_ = refl

-- three deep, shadowing the middle one
_ : elab "\\x. \\y. \\x. x" ≡ just (LT.lam (LT.lam (LT.lam (LT.var 0))))
_ = refl

_ : elab "\\x. \\y. \\z. x" ≡ just (LT.lam (LT.lam (LT.lam (LT.var 2))))
_ = refl

-- ---- application, parenthesised ------------------------------------
_ : elab "(\\f. \\a. (f a))"
  ≡ just (LT.lam (LT.lam (LT.app (LT.var 1) (LT.var 0))))
_ = refl

-- ---- annotations ---------------------------------------------------
_ : elab "((\\x. x) : (o -o o))"
  ≡ just (LT.ann (LT.lam (LT.var 0)) (LT.base LT.⊸ᵗ LT.base))
_ = refl

_ : elab "((\\x. x) : ((o -o o) -o (o -o o)))"
  ≡ just (LT.ann (LT.lam (LT.var 0))
                 ((LT.base LT.⊸ᵗ LT.base) LT.⊸ᵗ (LT.base LT.⊸ᵗ LT.base)))
_ = refl

-- ---- scope errors are `nothing`, and they are the RESOLVER's --------
_ : elab "\\x. y" ≡ nothing            -- `y` is free
_ = refl

_ : elab "x" ≡ nothing                 -- free at the top level
_ = refl

-- ---- parse errors are the PARSER's ---------------------------------
_ : elab "(\\x. x" ≡ nothing           -- unbalanced
_ = refl

_ : elab "\\x. x)" ≡ nothing           -- trailing paren
_ = refl

_ : elab "(x x x)" ≡ nothing           -- application is BINARY
_ = refl

-- ---- lexical errors are the SCANNER's ------------------------------
_ : elab "x @ y" ≡ nothing
_ = refl

-- ==================================================================
-- §3  THE FLAGSHIP, from a string.
--
-- `Chain.Rust.srcSelf` written by hand as a `Raw` was
--     app (ann (lam (var 0)) (oo ⊸ᵗ oo)) (lam (var 0))
-- and this is the same term, parsed.
-- ==================================================================

selfSrc : UString
selfSrc = "(((\\x. x) : ((o -o o) -o (o -o o))) (\\y. y))"

_ : elab selfSrc
  ≡ just (LT.app (LT.ann (LT.lam (LT.var 0))
                         ((LT.base LT.⊸ᵗ LT.base) LT.⊸ᵗ (LT.base LT.⊸ᵗ LT.base)))
                 (LT.lam (LT.var 0)))
_ = refl
