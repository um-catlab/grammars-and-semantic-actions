{-
  A parser for effect programs: terms of an algebraic signature written
  in applicative notation, the way real code looks.

    M ::= return v                 -- a value
        | do M                     -- a block, for readability
        | ( M )
        | op                       -- a nullary operation
        | op ; M                   -- a unary operation, in statement form
        | op ( M )                 -- a unary operation, in applied form
        | op ( M , M )             -- a binary operation

  So a program reads

    do s:=1; get(return 0, return 1)

  which is the term `put₁(look(ret 0, ret 1))` of the theory of state.

  An operation's arity is part of its identity: `Ops : Ar → Type` groups
  the operations by arity, so the grammar and the parser both know how
  many continuations to expect without any case analysis on a stuck
  `arity o`.  Arities are capped at 2, which covers state,
  nondeterminism and probability; a general n-ary version would replace
  `Ar` by ℕ and recurse on it in `appF` and in `opCase` below.

  As with `Parser.Precedence` this is one Löb-guarded fixed point.  Only
  one nonterminal is involved, so it is `fixP` directly.  Every recursive
  call is preceded by at least one literal — the `(`, the `;`, the `,`,
  the `do` — which is what makes it guarded.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Parser.Effects (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Maybe as Mb
import Cubical.Data.Sum as Sum

open import Grammar Alphabet hiding (Δ)
open import Grammar.Maybe.Base Alphabet hiding (μ)
open import Grammar.SemanticAction Alphabet
open import Grammar.Later.Base Alphabet
open import Grammar.Later.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Parser.Base Alphabet hiding (Parser)
open import Parser.RecursiveDescent Alphabet
open import Term Alphabet

open StrongEquivalence

------------------------------------------------------------------------------
-- Arities
------------------------------------------------------------------------------

data Ar : Type ℓ-zero where
  ar0 ar1 ar2 : Ar

isSetAr : isSet Ar
isSetAr = isSetRetract enc dec retr (Sum.isSet⊎ isSetBool isSetUnit)
  where
    enc : Ar → (Bool Sum.⊎ Unit)
    enc ar0 = Sum.inl true
    enc ar1 = Sum.inl false
    enc ar2 = Sum.inr tt
    dec : (Bool Sum.⊎ Unit) → Ar
    dec (Sum.inl true) = ar0
    dec (Sum.inl false) = ar1
    dec (Sum.inr tt) = ar2
    retr : (a : Ar) → dec (enc a) ≡ a
    retr ar0 = refl
    retr ar1 = refl
    retr ar2 = refl

-- The continuations an operation of each arity is applied to.
Args : ∀ {ℓ} → Ar → Type ℓ → Type ℓ
Args ar0 Y = Unit*
Args ar1 Y = Y
Args ar2 Y = Y × Y

data Tag : Type ℓ-zero where
  retT grpT blkT appT : Tag

isSetTag : isSet Tag
isSetTag = isSetRetract enc dec retr (Sum.isSet⊎ isSetBool isSetBool)
  where
    enc : Tag → (Bool Sum.⊎ Bool)
    enc retT = Sum.inl true
    enc grpT = Sum.inl false
    enc blkT = Sum.inr true
    enc appT = Sum.inr false
    dec : (Bool Sum.⊎ Bool) → Tag
    dec (Sum.inl true) = retT
    dec (Sum.inl false) = grpT
    dec (Sum.inr true) = blkT
    dec (Sum.inr false) = appT
    retr : (t : Tag) → dec (enc t) ≡ t
    retr retT = refl
    retr grpT = refl
    retr blkT = refl
    retr appT = refl

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

▷-map : A ⊢ B → ▷ A ⊢ ▷ B
▷-map f w α y y<w = f y (α y y<w)

------------------------------------------------------------------------------
-- The specification of an effect language
------------------------------------------------------------------------------

record EffectSyntax : Type (ℓ-suc ℓ-zero) where
  field
    Ops : Ar → Type ℓ-zero
    isSetOps : ∀ a → isSet (Ops a)
    OpG : (a : Ar) → Ops a → Grammar ℓ-zero

    -- the fixed vocabulary: `return`, `do`, `(`, `)`, `,`, `;`, values
    RetG DoG OpenG CloseG SepG SeqG ValG : Grammar ℓ-zero

    isSetGrammarOpG : ∀ a (o : Ops a) → isSetGrammar (OpG a o)
    isSetGrammarRet : isSetGrammar RetG
    isSetGrammarDo : isSetGrammar DoG
    isSetGrammarOpen : isSetGrammar OpenG
    isSetGrammarClose : isSetGrammar CloseG
    isSetGrammarSep : isSetGrammar SepG
    isSetGrammarSeq : isSetGrammar SeqG
    isSetGrammarVal : isSetGrammar ValG

    -- one-token lookahead, consulted in the order return, do, `(`, op
    asRet : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ RetG)
    asDo : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ DoG)
    asOpen : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ OpenG)
    asClose : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ CloseG)
    asSep : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ SepG)
    asSeq : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ SeqG)
    asVal : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ ValG)
    asOp : (c : ⟨ Alphabet ⟩)
      → Mb.Maybe (Σ[ a ∈ Ar ] Σ[ o ∈ Ops a ] (＂ c ＂ ⊢ OpG a o))

module Effects (S : EffectSyntax) where
  open EffectSyntax S

  ----------------------------------------------------------------------------
  -- The grammar
  --
  -- Every ⊗e is nested to the *left*, in the order the parser consumes
  -- tokens.  That way the constructors below are exactly the shapes the
  -- parser builds, and neither ever reassociates.
  ----------------------------------------------------------------------------

  appF : (a : Ar) → Ops a → SPFunctor Unit
  appF ar0 o = k (OpG ar0 o)
  appF ar1 o =
    ⊕e Bool
      λ where
        true → (k (OpG ar1 o) ⊗e k SeqG) ⊗e Var tt
        false → ((k (OpG ar1 o) ⊗e k OpenG) ⊗e Var tt) ⊗e k CloseG
  appF ar2 o =
    ((((k (OpG ar2 o) ⊗e k OpenG) ⊗e Var tt) ⊗e k SepG) ⊗e Var tt) ⊗e k CloseG

  Ty : Unit → SPFunctor Unit
  Ty _ =
    ⊕e Tag
      λ where
        retT → k RetG ⊗e k ValG
        grpT → (k OpenG ⊗e Var tt) ⊗e k CloseG
        blkT → k DoG ⊗e Var tt
        appT → ⊕e (Σ[ a ∈ Ar ] Ops a) λ ao → appF (ao .fst) (ao .snd)

  M : Grammar ℓ-zero
  M = μ Ty tt

  RET : RetG ⊗ ValG ⊢ M
  RET = roll ∘g σ retT ∘g liftG ,⊗ liftG

  GRP : (OpenG ⊗ M) ⊗ CloseG ⊢ M
  GRP = roll ∘g σ grpT ∘g (liftG ,⊗ liftG) ,⊗ liftG

  BLK : DoG ⊗ M ⊢ M
  BLK = roll ∘g σ blkT ∘g liftG ,⊗ liftG

  APP0 : (o : Ops ar0) → OpG ar0 o ⊢ M
  APP0 o = roll ∘g σ appT ∘g σ (ar0 , o) ∘g liftG

  APP1seq : (o : Ops ar1) → (OpG ar1 o ⊗ SeqG) ⊗ M ⊢ M
  APP1seq o =
    roll ∘g σ appT ∘g σ (ar1 , o) ∘g σ true ∘g (liftG ,⊗ liftG) ,⊗ liftG

  APP1par : (o : Ops ar1) → ((OpG ar1 o ⊗ OpenG) ⊗ M) ⊗ CloseG ⊢ M
  APP1par o =
    roll ∘g σ appT ∘g σ (ar1 , o) ∘g σ false
    ∘g ((liftG ,⊗ liftG) ,⊗ liftG) ,⊗ liftG

  APP2 : (o : Ops ar2)
    → ((((OpG ar2 o ⊗ OpenG) ⊗ M) ⊗ SepG) ⊗ M) ⊗ CloseG ⊢ M
  APP2 o =
    roll ∘g σ appT ∘g σ (ar2 , o)
    ∘g ((((liftG ,⊗ liftG) ,⊗ liftG) ,⊗ liftG) ,⊗ liftG) ,⊗ liftG

  isSetValuedAppF : ∀ a (o : Ops a) → isSetValued (appF a o)
  isSetValuedAppF ar0 o = isSetGrammarOpG ar0 o
  isSetValuedAppF ar1 o =
    isSetBool ,
    λ where
      true → (isSetGrammarOpG ar1 o , isSetGrammarSeq) , tt*
      false → ((isSetGrammarOpG ar1 o , isSetGrammarOpen) , tt*) , isSetGrammarClose
  isSetValuedAppF ar2 o =
    ((((isSetGrammarOpG ar2 o , isSetGrammarOpen) , tt*) , isSetGrammarSep) , tt*)
    , isSetGrammarClose

  isSetValuedTy : ∀ u → isSetValued (Ty u)
  isSetValuedTy _ =
    isSetTag ,
    λ where
      retT → isSetGrammarRet , isSetGrammarVal
      grpT → (isSetGrammarOpen , tt*) , isSetGrammarClose
      blkT → isSetGrammarDo , tt*
      appT →
        isSetΣ isSetAr isSetOps ,
        λ ao → isSetValuedAppF (ao .fst) (ao .snd)

  isSetGrammarM : isSetGrammar M
  isSetGrammarM = isSetGrammarμ Ty isSetValuedTy tt

  ----------------------------------------------------------------------------
  -- The parser
  ----------------------------------------------------------------------------

  Prs : Grammar ℓ-zero
  Prs = MaybeLeft M

  -- `K` is the run of tokens already recognised at the head of the input.
  -- Both combinators extend it on the right, so `K` is always
  -- left-nested in consumption order.

  -- Read one more token and dispatch on it.
  expectTok : ∀ {ℓK ℓR} {K : Grammar ℓK} {R : Grammar ℓR}
    → ((c : ⟨ Alphabet ⟩) → ▷ Prs & ((K ⊗ literal c) ⊗ string) ⊢ Maybe R)
    → ▷ Prs & (K ⊗ string) ⊢ Maybe R
  expectTok f =
    ⊕-elim
      (nothing ∘g ⊤-intro)
      (⊕ᴰ-elim (λ c → f c ∘g id ,&p ⊗-assoc)
       ∘g &⊕ᴰ-distR≅ .fun
       ∘g id ,&p ⊕ᴰ-distR .fun
       ∘g id ,&p (id ,⊗ ⊕ᴰ-distL .fun))
    ∘g &⊕-distL
    ∘g id ,&p ⊗⊕-distL
    ∘g id ,&p (id ,⊗ unroll-string≅ .fun)

  -- Parse one more term.  `K` is nonempty, so the term starts at a
  -- strict suffix and `▷` delivers the parser there.  The guarded
  -- parser is kept, so a continuation may parse further terms.
  parseAfter : ∀ {ℓK ℓR} {K : Grammar ℓK} {R : Grammar ℓR}
    → ⟨ ¬Nullable K ⟩
    → (▷ Prs & ((K ⊗ M) ⊗ string) ⊢ Maybe R)
    → ▷ Prs & (K ⊗ string) ⊢ Maybe R
  parseAfter ¬nullK f =
    ⊕-elim (f ∘g id ,&p ⊗-assoc) (nothing ∘g ⊤-intro)
    ∘g &⊕-distL
    ∘g π₁ ,& (⊗⊕-distL
              ∘g ▷-app-NE ¬nullK
              ∘g &-swap
              ∘g id ,&p (id ,⊗ ⊤-intro))

  private
    fail : ∀ {ℓK ℓR} {K : Grammar ℓK} {R : Grammar ℓR}
      → ▷ Prs & K ⊢ Maybe R
    fail = nothing ∘g ⊤-intro

  module _ (c : ⟨ Alphabet ⟩) where

    -- `return v`
    retCase : (＂ c ＂ ⊢ RetG) → ▷ Prs & (＂ c ＂ ⊗ string) ⊢ Prs
    retCase inj = expectTok value
      where
        value : (d : ⟨ Alphabet ⟩) →
          ▷ Prs & ((＂ c ＂ ⊗ literal d) ⊗ string) ⊢ Prs
        value d = go (asVal d)
          where
            go : Mb.Maybe (＂ d ＂ ⊢ ValG) →
              ▷ Prs & ((＂ c ＂ ⊗ literal d) ⊗ string) ⊢ Prs
            go Mb.nothing = fail
            go (Mb.just vinj) = just ∘g (RET ∘g inj ,⊗ vinj) ,⊗ id ∘g π₂

    -- `do M`
    blkCase : (＂ c ＂ ⊢ DoG) → ▷ Prs & (＂ c ＂ ⊗ string) ⊢ Prs
    blkCase inj =
      parseAfter (disjoint-ε-literal c)
        (just ∘g (BLK ∘g inj ,⊗ id) ,⊗ id ∘g π₂)

    -- `( M )`
    grpCase : (＂ c ＂ ⊢ OpenG) → ▷ Prs & (＂ c ＂ ⊗ string) ⊢ Prs
    grpCase inj = parseAfter (disjoint-ε-literal c) (expectTok close)
      where
        close : (d : ⟨ Alphabet ⟩) →
          ▷ Prs & (((＂ c ＂ ⊗ M) ⊗ literal d) ⊗ string) ⊢ Prs
        close d = go (asClose d)
          where
            go : Mb.Maybe (＂ d ＂ ⊢ CloseG) →
              ▷ Prs & (((＂ c ＂ ⊗ M) ⊗ literal d) ⊗ string) ⊢ Prs
            go Mb.nothing = fail
            go (Mb.just cinj) =
              just ∘g (GRP ∘g (inj ,⊗ id) ,⊗ cinj) ,⊗ id ∘g π₂

    -- `op`
    op0Case : (o : Ops ar0) → (＂ c ＂ ⊢ OpG ar0 o)
      → ▷ Prs & (＂ c ＂ ⊗ string) ⊢ Prs
    op0Case o inj = just ∘g (APP0 o ∘g inj) ,⊗ id ∘g π₂

    -- `op ; M`  or  `op ( M )`
    op1Case : (o : Ops ar1) → (＂ c ＂ ⊢ OpG ar1 o)
      → ▷ Prs & (＂ c ＂ ⊗ string) ⊢ Prs
    op1Case o inj = expectTok next
      where
        next : (d : ⟨ Alphabet ⟩) →
          ▷ Prs & ((＂ c ＂ ⊗ literal d) ⊗ string) ⊢ Prs
        next d = go (asSeq d) (asOpen d)
          where
            nonNull : ⟨ ¬Nullable (＂ c ＂ ⊗ ＂ d ＂) ⟩
            nonNull = ¬Nullable⊗r (disjoint-ε-literal d)

            close : (＂ d ＂ ⊢ OpenG) → (e : ⟨ Alphabet ⟩) →
              ▷ Prs & (((( ＂ c ＂ ⊗ literal d) ⊗ M) ⊗ literal e) ⊗ string) ⊢ Prs
            close oinj e = go' (asClose e)
              where
                go' : Mb.Maybe (＂ e ＂ ⊢ CloseG) →
                  ▷ Prs
                  & (((( ＂ c ＂ ⊗ literal d) ⊗ M) ⊗ literal e) ⊗ string) ⊢ Prs
                go' Mb.nothing = fail
                go' (Mb.just cinj) =
                  just
                  ∘g (APP1par o ∘g ((inj ,⊗ oinj) ,⊗ id) ,⊗ cinj) ,⊗ id
                  ∘g π₂

            go : Mb.Maybe (＂ d ＂ ⊢ SeqG) → Mb.Maybe (＂ d ＂ ⊢ OpenG) →
              ▷ Prs & ((＂ c ＂ ⊗ literal d) ⊗ string) ⊢ Prs
            go (Mb.just sinj) _ =
              parseAfter nonNull
                (just ∘g (APP1seq o ∘g (inj ,⊗ sinj) ,⊗ id) ,⊗ id ∘g π₂)
            go Mb.nothing (Mb.just oinj) =
              parseAfter nonNull (expectTok (close oinj))
            go Mb.nothing Mb.nothing = fail

    -- `op ( M , M )`
    op2Case : (o : Ops ar2) → (＂ c ＂ ⊢ OpG ar2 o)
      → ▷ Prs & (＂ c ＂ ⊗ string) ⊢ Prs
    op2Case o inj = expectTok open?
      where
        open? : (d : ⟨ Alphabet ⟩) →
          ▷ Prs & ((＂ c ＂ ⊗ literal d) ⊗ string) ⊢ Prs
        open? d = go (asOpen d)
          where
            nonNull : ⟨ ¬Nullable (＂ c ＂ ⊗ ＂ d ＂) ⟩
            nonNull = ¬Nullable⊗r (disjoint-ε-literal d)

            module _ (oinj : ＂ d ＂ ⊢ OpenG) where
              close : (e : ⟨ Alphabet ⟩) (seinj : ＂ e ＂ ⊢ SepG)
                (f : ⟨ Alphabet ⟩) →
                ▷ Prs
                & ((((((＂ c ＂ ⊗ literal d) ⊗ M) ⊗ literal e) ⊗ M)
                    ⊗ literal f) ⊗ string)
                ⊢ Prs
              close e seinj f = go' (asClose f)
                where
                  go' : Mb.Maybe (＂ f ＂ ⊢ CloseG) →
                    ▷ Prs
                    & ((((((＂ c ＂ ⊗ literal d) ⊗ M) ⊗ literal e) ⊗ M)
                        ⊗ literal f) ⊗ string)
                    ⊢ Prs
                  go' Mb.nothing = fail
                  go' (Mb.just cinj) =
                    just
                    ∘g (APP2 o
                        ∘g (((((inj ,⊗ oinj) ,⊗ id) ,⊗ seinj) ,⊗ id) ,⊗ cinj))
                       ,⊗ id
                    ∘g π₂

              sep : (e : ⟨ Alphabet ⟩) →
                ▷ Prs & (((( ＂ c ＂ ⊗ literal d) ⊗ M) ⊗ literal e) ⊗ string)
                ⊢ Prs
              sep e = go' (asSep e)
                where
                  go' : Mb.Maybe (＂ e ＂ ⊢ SepG) →
                    ▷ Prs
                    & (((( ＂ c ＂ ⊗ literal d) ⊗ M) ⊗ literal e) ⊗ string)
                    ⊢ Prs
                  go' Mb.nothing = fail
                  go' (Mb.just seinj) =
                    parseAfter (¬Nullable⊗r (disjoint-ε-literal e))
                      (expectTok (close e seinj))

            go : Mb.Maybe (＂ d ＂ ⊢ OpenG) →
              ▷ Prs & ((＂ c ＂ ⊗ literal d) ⊗ string) ⊢ Prs
            go Mb.nothing = fail
            go (Mb.just oinj) = parseAfter nonNull (expectTok (sep oinj))

    head : ▷ Prs & (literal c ⊗ string) ⊢ Prs
    head = go (asRet c) (asDo c) (asOpen c) (asOp c)
      where
        go : Mb.Maybe (＂ c ＂ ⊢ RetG) → Mb.Maybe (＂ c ＂ ⊢ DoG)
           → Mb.Maybe (＂ c ＂ ⊢ OpenG)
           → Mb.Maybe (Σ[ a ∈ Ar ] Σ[ o ∈ Ops a ] (＂ c ＂ ⊢ OpG a o))
           → ▷ Prs & (literal c ⊗ string) ⊢ Prs
        go (Mb.just inj) _ _ _ = retCase inj
        go Mb.nothing (Mb.just inj) _ _ = blkCase inj
        go Mb.nothing Mb.nothing (Mb.just inj) _ = grpCase inj
        go Mb.nothing Mb.nothing Mb.nothing (Mb.just (ar0 , o , inj)) =
          op0Case o inj
        go Mb.nothing Mb.nothing Mb.nothing (Mb.just (ar1 , o , inj)) =
          op1Case o inj
        go Mb.nothing Mb.nothing Mb.nothing (Mb.just (ar2 , o , inj)) =
          op2Case o inj
        go Mb.nothing Mb.nothing Mb.nothing Mb.nothing = fail

  step : ▷ Prs & string ⊢ Prs
  step =
    ⊕-elim
      (nothing ∘g ⊤-intro)
      (⊕ᴰ-elim head
       ∘g &⊕ᴰ-distR≅ .fun
       ∘g id ,&p ⊕ᴰ-distL .fun)
    ∘g &⊕-distL
    ∘g id ,&p unroll-string≅ .fun

  parseM : Parser M
  parseM = fixP isSetGrammarM (step ∘g id ,& string-intro)

  recognize : string ⊢ Maybe M
  recognize = parse parseM

  ----------------------------------------------------------------------------
  -- The generic semantic action
  ----------------------------------------------------------------------------

  module Semantics {ℓY} (Y : Type ℓY)
    (valSem : SemanticAction ValG Y)
    (opSem : (a : Ar) (o : Ops a) → Args a Y → Y)
    where

    semAlg : ∀ u → ⟦ Ty u ⟧ (λ _ → Δ Y) ⊢ Δ Y
    semAlg _ = ⊕ᴰ-elim λ where
      retT → semact-right (semact-lift valSem)
      grpT → semact-left (semact-right (semact-lift semact-Δ))
      blkT → semact-right (semact-lift semact-Δ)
      appT → ⊕ᴰ-elim λ where
        (ar0 , o) → semact-pure (opSem ar0 o tt*)
        (ar1 , o) → ⊕ᴰ-elim λ where
          true →
            semact-map (opSem ar1 o)
              (semact-right (semact-lift semact-Δ))
          false →
            semact-map (opSem ar1 o)
              (semact-left (semact-right (semact-lift semact-Δ)))
        (ar2 , o) →
          semact-map (opSem ar2 o)
            (semact-left
              (semact-concat
                (semact-left (semact-right (semact-lift semact-Δ)))
                (semact-lift semact-Δ)))

    eval : M ⊢ Δ Y
    eval = semact-rec semAlg tt

    evaluate : string ⊢ Maybe (Δ Y)
    evaluate = fmap eval ∘g recognize
