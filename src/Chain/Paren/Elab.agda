{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PARSE, CONSUMED BY A SEMANTIC ACTION THE NEXT PASS SUPPLIES.

  The parser produces a derivation of `Grammar.Trm`.  What a later phase
  wants out of it differs -- a named tree for a diagnostic, a de Bruijn
  term for the typechecker -- and the wrong way to serve both is to fix
  ONE syntax tree here and re-traverse it downstream.  Then the parens
  are elided by a metalanguage recursion, scope resolution is a second
  recursion over a datatype nobody asked for, and each pass re-reads what
  the last one wrote.

  So this file fixes NO tree.  It exposes

      record SynAlg (T Y : Type₀)      -- what to build at each production
      readWith : SynAlg T Y → Trm ⊢ Δ T

  -- ONE fold, parameterised by the algebra its consumer hands in.  The
  parentheses and the `:` are elided by `drop` inside that fold, which is
  a semantic action (`pureA Unit tt`) and not a rewrite: the punctuation
  is never built, so nothing downstream has to remove it.

  ==================================================================
  THE TWO ALGEBRAS, AND WHAT THE SECOND ONE SHOWS.

      namedAlg : SynAlg NTm NTy                         -- the initial one
      dbAlg    : SynAlg (Env → Maybe LT.Raw) LT.Ty      -- scope resolution

  `dbAlg`'s carrier is a FUNCTION FROM THE ENVIRONMENT, so name
  resolution is not a pass after the parse -- it IS the parse's action,
  fused.  There is no named tree in between, and

      lamA n b = λ e → mapMb LT.lam (b (n ∷ e))

  is the entire shadowing story: the body is read in an environment the
  binder has already been pushed onto, and `lookupN` takes the FIRST
  match, so an inner `\x.` wins over an outer one.  A free name is a
  `nothing`, so this is also the scope check -- the de Bruijn index it
  produces is in range by construction of the environment.

  `namedAlg` is kept because a diagnostic wants the names back
  (`Chain.TypeLocate`'s site), and it costs one record.

  ==================================================================
  WHY THE NAMES WERE THERE TO READ.  `decμ` needs a FINITE alternative
  set, so names could not be alternatives; `Grammar` put them in the
  witnesses of `VarTok` and `Binder`, and `nameOfVar`/`nameOfBinder`
  project them back out of the shape the parser already produced.

  PHASE.  The branches are pointful in the PAYLOAD and not in the index:
  the motive is `Δ`, a constant family, which is the sanctioned case for
  a semantic action.  §3's `lookupN` is phase 1 and marked.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Elab where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import TheoryGrammar.SemanticAction
open import TheoryGrammar.Inductive

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar

open ActFib strFib

import TheoryGrammar.Instances.LinTyped as LT

-- ==================================================================
-- §1  WHAT A CONSUMER SUPPLIES.  Six clauses, one per production --
-- and no clause for a parenthesis, because the fold never offers one.
-- ==================================================================

record SynAlg (T Y : Type₀) : Type₀ where
  field
    varA  : Name → T
    lamA  : Name → T → T
    appA  : T → T → T
    annA  : T → Y → T
    baseA : Y
    arrA  : Y → Y → Y

open SynAlg public

-- ==================================================================
-- §2  THE FOLD.  `⊕ᴰ-E` over the alternatives, `⊗A` per product, with
-- each slot saying what it CONTRIBUTES -- `Unit` for punctuation.
-- ==================================================================

module Read {T Y : Type₀} (α : SynAlg T Y) where

  Z : NT → Type₀
  Z ntm = T
  Z nty = Y

  module AI = ActInd strFib ℓ-zero NT (λ _ → tt)

  Mot : Ix → Type₀
  Mot i = Δ (Z (i .fst)) (i .snd)

  private
    drop : {A : Gr} → Action A Unit
    drop = pureA Unit tt

  -- PRIMITIVE (phase 1): the name-carrying constants, READ.  The
  -- witness IS the name, so this is a projection and not a lookup.
  nameOfVar : ⟦ ⌜ VarTok ⌝ ⟧c Mot ⊢ Δ Name
  nameOfVar m x = lower x .fst , tt

  nameOfBinder : ⟦ ⌜ Binder ⌝ ⟧c Mot ⊢ Δ Name
  nameOfBinder m x = lower x .fst , tt

  parenAlg : AI.ActAlg parenF Z

  parenAlg ntm = ⊕ᴰ-E branch
    where
    Lm A3 A2 A1 E4 E3 E2 E1 : Bool → Type₀
    Lm true  = Name ; Lm false = T
    A3 true  = T    ; A3 false = Unit
    A2 true  = T    ; A2 false = T
    A1 true  = Unit ; A1 false = T × T
    E4 true  = Y    ; E4 false = Unit
    E3 true  = Unit ; E3 false = Y
    E2 true  = T    ; E2 false = Y
    E1 true  = Unit ; E1 false = T × Y

    bLam : ⟦ ⊗e appop lamF ⟧c Mot ⊢ Δ T
    bLam = mapA (λ f → α .lamA (f true) (f false))
           (⊗A appop {A = λ b → ⟦ lamF b ⟧c Mot} Lm
               (λ { true → nameOfBinder ; false → idA }))

    a3 : ⟦ ⊗e appop app₃ ⟧c Mot ⊢ Δ T
    a3 = mapA (λ f → f true)
         (⊗A appop {A = λ b → ⟦ app₃ b ⟧c Mot} A3
             (λ { true → idA ; false → drop }))

    a2 : ⟦ ⊗e appop app₂ ⟧c Mot ⊢ Δ (T × T)
    a2 = mapA (λ f → f true , f false)
         (⊗A appop {A = λ b → ⟦ app₂ b ⟧c Mot} A2
             (λ { true → idA ; false → a3 }))

    a1 : ⟦ ⊗e appop app₁ ⟧c Mot ⊢ Δ T
    a1 = mapA (λ f → α .appA (f false .fst) (f false .snd))
         (⊗A appop {A = λ b → ⟦ app₁ b ⟧c Mot} A1
             (λ { true → drop ; false → a2 }))

    e4 : ⟦ ⊗e appop ann₄ ⟧c Mot ⊢ Δ Y
    e4 = mapA (λ f → f true)
         (⊗A appop {A = λ b → ⟦ ann₄ b ⟧c Mot} E4
             (λ { true → idA ; false → drop }))

    e3 : ⟦ ⊗e appop ann₃ ⟧c Mot ⊢ Δ Y
    e3 = mapA (λ f → f false)
         (⊗A appop {A = λ b → ⟦ ann₃ b ⟧c Mot} E3
             (λ { true → drop ; false → e4 }))

    e2 : ⟦ ⊗e appop ann₂ ⟧c Mot ⊢ Δ (T × Y)
    e2 = mapA (λ f → f true , f false)
         (⊗A appop {A = λ b → ⟦ ann₂ b ⟧c Mot} E2
             (λ { true → idA ; false → e3 }))

    e1 : ⟦ ⊗e appop ann₁ ⟧c Mot ⊢ Δ T
    e1 = mapA (λ f → α .annA (f false .fst) (f false .snd))
         (⊗A appop {A = λ b → ⟦ ann₁ b ⟧c Mot} E1
             (λ { true → drop ; false → e2 }))

    P1 : Bool → Type₀
    P1 true = Unit ; P1 false = T

    p2' : ⟦ ⊗e appop par₂ ⟧c Mot ⊢ Δ T
    p2' = mapA (λ f → f true)
          (⊗A appop {A = λ b → ⟦ par₂ b ⟧c Mot} A3
              (λ { true → idA ; false → drop }))

    p1' : ⟦ ⊗e appop par₁ ⟧c Mot ⊢ Δ T
    p1' = mapA (λ f → f false)
          (⊗A appop {A = λ b → ⟦ par₁ b ⟧c Mot} P1
              (λ { true → drop ; false → p2' }))

    branch : (a : AltT) → ⟦ bodyT a ⟧c Mot ⊢ Δ T
    branch aPar = p1'
    branch aVar = mapA (α .varA) nameOfVar
    branch aLam = bLam
    branch aApp = a1
    branch aAnn = e1

  parenAlg nty = ⊕ᴰ-E branch
    where
    R4 R3 R2 R1 : Bool → Type₀
    R4 true  = Y    ; R4 false = Unit
    R3 true  = Unit ; R3 false = Y
    R2 true  = Y    ; R2 false = Y
    R1 true  = Unit ; R1 false = Y × Y

    r4 : ⟦ ⊗e appop arr₄ ⟧c Mot ⊢ Δ Y
    r4 = mapA (λ f → f true)
         (⊗A appop {A = λ b → ⟦ arr₄ b ⟧c Mot} R4
             (λ { true → idA ; false → drop }))

    r3 : ⟦ ⊗e appop arr₃ ⟧c Mot ⊢ Δ Y
    r3 = mapA (λ f → f false)
         (⊗A appop {A = λ b → ⟦ arr₃ b ⟧c Mot} R3
             (λ { true → drop ; false → r4 }))

    r2 : ⟦ ⊗e appop arr₂ ⟧c Mot ⊢ Δ (Y × Y)
    r2 = mapA (λ f → f true , f false)
         (⊗A appop {A = λ b → ⟦ arr₂ b ⟧c Mot} R2
             (λ { true → idA ; false → r3 }))

    r1 : ⟦ ⊗e appop arr₁ ⟧c Mot ⊢ Δ Y
    r1 = mapA (λ f → α .arrA (f false .fst) (f false .snd))
         (⊗A appop {A = λ b → ⟦ arr₁ b ⟧c Mot} R1
             (λ { true → drop ; false → r2 }))

    branch : (a : AltY) → ⟦ bodyY a ⟧c Mot ⊢ Δ Y
    branch yBase = pureA Y (α .baseA)
    branch yArr  = r1

  readT : Trm ⊢ Δ T
  readT = AI.recA parenAlg ntm

open Read public using () renaming (readT to readWith')

-- the reader, with the algebra explicit
readWith : {T Y : Type₀} → SynAlg T Y → Trm ⊢ Δ T
readWith α = Read.readT α

-- ==================================================================
-- §3  THE ALGEBRA THE NEXT PASS SUPPLIES: SCOPE RESOLUTION.
--
-- The carrier is a FUNCTION FROM THE ENVIRONMENT, so resolution fuses
-- into the parse rather than following it.  There is no named tree.
-- ==================================================================

Env : Type₀
Env = List Name

mapMb : {A B : Type₀} → (A → B) → Maybe A → Maybe B
mapMb f (just a) = just (f a)
mapMb f nothing  = nothing

-- PRIMITIVE (phase 1): FIRST match wins.  The environment is
-- innermost-first, so an inner binder of the same name shadows an outer
-- one, and a name that is absent is `nothing` -- the scope check.
lookupN : Env → Name → Maybe ℕ
lookupN []      n = nothing
lookupN (m ∷ e) n with decName m n
... | inl _ = just 0
... | inr _ = mapMb suc (lookupN e n)

Res : Type₀
Res = Env → Maybe LT.Raw

dbAlg : SynAlg Res LT.Ty
dbAlg .varA n   = λ e → mapMb LT.var (lookupN e n)
dbAlg .lamA n b = λ e → mapMb LT.lam (b (n ∷ e))
dbAlg .appA f a = λ e → ap2 (f e) (a e)
  where ap2 : Maybe LT.Raw → Maybe LT.Raw → Maybe LT.Raw
        ap2 (just u) (just v) = just (LT.app u v)
        ap2 _        _        = nothing
dbAlg .annA t T = λ e → mapMb (λ r → LT.ann r T) (t e)
dbAlg .baseA    = LT.base
dbAlg .arrA a b = a LT.⊸ᵗ b

-- THE ACTION the typechecker consumes: a derivation to a de Bruijn term.
toRaw : Trm ⊢ Δ Res
toRaw = readWith dbAlg

-- ==================================================================
-- §4  ... AND THE ONE A DIAGNOSTIC CONSUMES: the names, kept.
-- ==================================================================

data NTy : Type₀ where
  nbase : NTy
  narr  : NTy → NTy → NTy

data NTm : Type₀ where
  nvar : Name → NTm
  nlam : Name → NTm → NTm
  napp : NTm → NTm → NTm
  nann : NTm → NTy → NTm

namedAlg : SynAlg NTm NTy
namedAlg .varA    = nvar
namedAlg .lamA    = nlam
namedAlg .appA    = napp
namedAlg .annA    = nann
namedAlg .baseA   = nbase
namedAlg .arrA    = narr

toNamed : Trm ⊢ Δ NTm
toNamed = readWith namedAlg
