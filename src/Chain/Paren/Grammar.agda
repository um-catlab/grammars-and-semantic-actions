{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PARSER FOR LINEAR STLC, AS A `μ` DECIDED BY `decμ`.

  Two nonterminals, six productions, fully parenthesised:

      trm ::=  id                        aVar
            |  \ id . trm                aLam
            |  ( trm trm )               aApp
            |  ( trm : ty )              aAnn
      ty  ::=  o                         yBase
            |  ( ty -o ty )              yArr

  `Chain.Paren.Tokens` is the alphabet; this file is the grammar and the
  decision, and `Chain.Paren.Elab` reads a tree out of it.

  ==================================================================
  WHY FULLY PARENTHESISED, AND IT IS NOT A MATTER OF TASTE.

  `decμ`'s obligation is `GuardedD`: every recursive occurrence must sit
  at a STRICTLY SHORTER word.  In a spine grammar (`trm ::= atom rest`)
  the first occurrence is at the START of its production, so its word can
  be the whole input and the obligation is unprovable without a FIRST-set
  lemma threaded through a nonterminal.  Parenthesising puts a LITERAL
  TOKEN before every recursive occurrence, so `split3LenR<` discharges it
  and `parenGuarded` is the argument -- the same shape as
  `Strings.DyckDec.dyckGuarded`, three and four levels deep.

  It also makes the grammar unambiguous, which is the other half: the
  ambiguity of `Lambda.Parse` is what forced the CYK chart, refuted
  `Section` for the printer (`Chain.PrintTests.notInjective`), and made
  the chain's own reprint fail to decide in seven minutes.

  ==================================================================
  WHERE THE NAMES LIVE, and it is deliberate.

  `decμ` needs `Listed (Alt x)`, so the alternative set must be FINITE --
  four and two.  Names are therefore NOT alternatives; they sit in the
  witnesses of two constants,

      VarTok w  =  Σ[ n ] w ≡ [ id n ]
      Binder w  =  Σ[ n ] w ≡ [ \ , id n , . ]

  both decidable by inspection.  So the grammar admits ARBITRARY names
  with a finite description, and `Chain.Paren.Elab` reads each name back
  out of the witness the parser already produced.

  SHADOWING costs this file nothing: the parser produces a NAMED tree
  and resolution is `Elab`'s business.

  PHASE.  The description, the guardedness and the probes are phase 1 --
  they BUILD the grammar.  `parseTrm` is a `Probe`, i.e. a term.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Grammar where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed
open import TheoryGrammar.Decidable.Inductive
open import TheoryGrammar.SemanticAction

open import Chain.Paren.Tokens

-- The Ind names (`Functor`, `Var`, `μ`, `Sh`, `Ix`, ...) must come from
-- `DecInd` at X = NT.  `Strings.Graded` opens `Guard` at X = Unit, so it
-- is imported QUALIFIED and only its theory-level names are taken --
-- otherwise every former below would be the one-nonterminal instance.
import TheoryGrammar.Instances.Strings.Enumeration Tok as En
open En public using ( String ; MonOp ; nilop ; appop ; MonAr ; MonSplit ; MonParts
              ; strFib ; strGraded ; Gr ; ⌈_⌉
              ; enumSplit ; enumComplete
              ; split3LenL ; split3LenR ; split3LenR<
              ; ⊕ᴰ-E ; ⊗ˢ ; splitAll ; Split3 )

-- ==================================================================
-- §1  THE THEORY'S OBLIGATION, discharged once.
-- ==================================================================

enumSplitL : (o : MonOp) (m : String) → Listed (MonSplit o m)
enumSplitL o m .elts     = enumSplit o m
enumSplitL o m .complete = enumComplete o m

enumArL : (o : MonOp) → Listed (MonAr o)
enumArL nilop .elts     = []
enumArL nilop .complete = λ ()
enumArL appop .elts     = true ∷ false ∷ []
enumArL appop .complete true  = here
enumArL appop .complete false = there here

-- the two nonterminals
data NT : Type₀ where
  ntm nty : NT

-- opened in FULL: this is where `Functor`, `Var`, `⌜_⌝`, `⊗e`, `⊕e`,
-- `μ`, `Sh`, `Ix`, `degIx` and `Probe` come from, all at X = NT.
open DecInd strGraded ℓ-zero NT (λ _ → tt) enumSplitL enumArL public

-- ==================================================================
-- §2  THE CONSTANTS.  Four literals and two name-carrying shapes.
-- ==================================================================

Lit : Tok → Gr
Lit t = ⌈ t ∷ [] ⌉

-- PRIMITIVE (phase 1): an identifier token, CARRYING its name.
VarTok : Gr
VarTok w = Σ[ n ∈ Name ] (w Eq.≡ (tid n ∷ []))

-- PRIMITIVE (phase 1): the three-token binder prefix `\ n .`, carrying
-- the bound name.  This is where arbitrary names enter the grammar
-- without making the alternative set infinite.
Binder : Gr
Binder w = Σ[ n ∈ Name ] (w Eq.≡ (tlam ∷ tid n ∷ tdot ∷ []))

-- ==================================================================
-- §3  THE DESCRIPTION.  `⊗e` is binary, so an n-factor production is
-- (n-1) nested `⊗e`s, right-associated -- `Strings.DyckDec`'s shape.
-- ==================================================================

data AltT : Type₀ where aVar aLam aApp aAnn aPar : AltT
data AltY : Type₀ where yBase yArr : AltY

-- ---- \ id . trm ----------------------------------------------------
lamF : Bool → Functor tt
lamF true  = ⌜ Binder ⌝
lamF false = Var ntm

-- ---- ( trm trm ) ---------------------------------------------------
app₃ : Bool → Functor tt          -- trm ⊗ ')'
app₃ true  = Var ntm
app₃ false = ⌜ Lit trp ⌝

app₂ : Bool → Functor tt          -- trm ⊗ (trm ⊗ ')')
app₂ true  = Var ntm
app₂ false = ⊗e appop app₃

app₁ : Bool → Functor tt          -- '(' ⊗ (trm ⊗ (trm ⊗ ')'))
app₁ true  = ⌜ Lit tlp ⌝
app₁ false = ⊗e appop app₂

-- ---- ( trm ) -- grouping, so a lambda may be parenthesised ---------
par₂ : Bool → Functor tt          -- trm ⊗ ')'
par₂ true  = Var ntm
par₂ false = ⌜ Lit trp ⌝

par₁ : Bool → Functor tt          -- '(' ⊗ (trm ⊗ ')')
par₁ true  = ⌜ Lit tlp ⌝
par₁ false = ⊗e appop par₂

-- ---- ( trm : ty ) --------------------------------------------------
ann₄ : Bool → Functor tt          -- ty ⊗ ')'
ann₄ true  = Var nty
ann₄ false = ⌜ Lit trp ⌝

ann₃ : Bool → Functor tt          -- ':' ⊗ (ty ⊗ ')')
ann₃ true  = ⌜ Lit tcolon ⌝
ann₃ false = ⊗e appop ann₄

ann₂ : Bool → Functor tt          -- trm ⊗ (':' ⊗ (ty ⊗ ')'))
ann₂ true  = Var ntm
ann₂ false = ⊗e appop ann₃

ann₁ : Bool → Functor tt          -- '(' ⊗ ...
ann₁ true  = ⌜ Lit tlp ⌝
ann₁ false = ⊗e appop ann₂

-- ---- ( ty -o ty ) --------------------------------------------------
arr₄ : Bool → Functor tt          -- ty ⊗ ')'
arr₄ true  = Var nty
arr₄ false = ⌜ Lit trp ⌝

arr₃ : Bool → Functor tt          -- '-o' ⊗ (ty ⊗ ')')
arr₃ true  = ⌜ Lit tarrow ⌝
arr₃ false = ⊗e appop arr₄

arr₂ : Bool → Functor tt          -- ty ⊗ ('-o' ⊗ (ty ⊗ ')'))
arr₂ true  = Var nty
arr₂ false = ⊗e appop arr₃

arr₁ : Bool → Functor tt          -- '(' ⊗ ...
arr₁ true  = ⌜ Lit tlp ⌝
arr₁ false = ⊗e appop arr₂

-- ---- the two alternative families ----------------------------------
bodyT : AltT → Functor tt
bodyT aVar = ⌜ VarTok ⌝
bodyT aLam = ⊗e appop lamF
bodyT aApp = ⊗e appop app₁
bodyT aAnn = ⊗e appop ann₁
bodyT aPar = ⊗e appop par₁

bodyY : AltY → Functor tt
bodyY yBase = ⌜ Lit tbase ⌝
bodyY yArr  = ⊗e appop arr₁

parenF : NT → Functor tt
parenF ntm = ⊕e AltT bodyT
parenF nty = ⊕e AltY bodyY

-- THE GRAMMARS.
Trm TyG : Gr
Trm w = μ parenF (ntm , w)
TyG w = μ parenF (nty , w)

-- ==================================================================
-- §4  GUARDEDNESS.  The file's real proof, and it is `DyckDec`'s
-- argument at four productions instead of one.
-- ==================================================================

private
  Ok : String → Ix → Type₀
  Ok m j = degIx j < length m

  -- a one-token literal pins its factor to length 1
  lenLit : (t : Tok) {u : String} → Sh (⌜ Lit t ⌝) u → 0 < length u
  lenLit t sh = go (lower sh)
    where go : {u : String} → u Eq.≡ (t ∷ []) → 0 < length u
          go Eq.refl = ≤-refl

  -- ... and the binder prefix to length 3
  lenBinder : {u : String} → Sh (⌜ Binder ⌝) u → 0 < length u
  lenBinder sh = go (lower sh)
    where go : {u : String} → Binder u → 0 < length u
          go (n , Eq.refl) = suc-≤-suc zero-≤

parenGuarded : (x : NT) (m : String) → GuardedD (parenF x) m

-- ---- trm -----------------------------------------------------------
parenGuarded ntm m aVar = tt*

parenGuarded ntm m aLam = g
  where
  g : (sp : MonSplit appop m)
    → ((a : Bool) → Sh (lamF a) (MonParts appop m sp a))
    → (a : Bool) → Reaches (lamF a) (MonParts appop m sp a) (Ok m)
  g (u , v , s) shs true  = tt*
  g (u , v , s) shs false = lift (split3LenR< s (lenBinder (shs true)))

parenGuarded ntm m aApp = g₁
  where
  g₁ : (sp : MonSplit appop m)
     → ((a : Bool) → Sh (app₁ a) (MonParts appop m sp a))
     → (a : Bool) → Reaches (app₁ a) (MonParts appop m sp a) (Ok m)
  g₁ (u , v , s) shs true  = tt*
  g₁ (u , v , s) shs false = g₂
    where
    vLt : length v < length m
    vLt = split3LenR< s (lenLit tlp (shs true))

    g₂ : (sp₂ : MonSplit appop v)
       → ((a : Bool) → Sh (app₂ a) (MonParts appop v sp₂ a))
       → (a : Bool) → Reaches (app₂ a) (MonParts appop v sp₂ a) (Ok m)
    g₂ (u₂ , v₂ , s₂) shs₂ true  = lift (≤<-trans (split3LenL s₂) vLt)
    g₂ (u₂ , v₂ , s₂) shs₂ false = g₃
      where
      g₃ : (sp₃ : MonSplit appop v₂)
         → ((a : Bool) → Sh (app₃ a) (MonParts appop v₂ sp₃ a))
         → (a : Bool) → Reaches (app₃ a) (MonParts appop v₂ sp₃ a) (Ok m)
      g₃ (u₃ , v₃ , s₃) shs₃ true  =
        lift (≤<-trans (≤-trans (split3LenL s₃) (split3LenR s₂)) vLt)
      g₃ (u₃ , v₃ , s₃) shs₃ false = tt*

parenGuarded ntm m aAnn = h₁
  where
  h₁ : (sp : MonSplit appop m)
     → ((a : Bool) → Sh (ann₁ a) (MonParts appop m sp a))
     → (a : Bool) → Reaches (ann₁ a) (MonParts appop m sp a) (Ok m)
  h₁ (u , v , s) shs true  = tt*
  h₁ (u , v , s) shs false = h₂
    where
    vLt : length v < length m
    vLt = split3LenR< s (lenLit tlp (shs true))

    h₂ : (sp₂ : MonSplit appop v)
       → ((a : Bool) → Sh (ann₂ a) (MonParts appop v sp₂ a))
       → (a : Bool) → Reaches (ann₂ a) (MonParts appop v sp₂ a) (Ok m)
    h₂ (u₂ , v₂ , s₂) shs₂ true  = lift (≤<-trans (split3LenL s₂) vLt)
    h₂ (u₂ , v₂ , s₂) shs₂ false = h₃
      where
      v₂Lt : length v₂ < length m
      v₂Lt = ≤<-trans (split3LenR s₂) vLt

      h₃ : (sp₃ : MonSplit appop v₂)
         → ((a : Bool) → Sh (ann₃ a) (MonParts appop v₂ sp₃ a))
         → (a : Bool) → Reaches (ann₃ a) (MonParts appop v₂ sp₃ a) (Ok m)
      h₃ (u₃ , v₃ , s₃) shs₃ true  = tt*
      h₃ (u₃ , v₃ , s₃) shs₃ false = h₄
        where
        h₄ : (sp₄ : MonSplit appop v₃)
           → ((a : Bool) → Sh (ann₄ a) (MonParts appop v₃ sp₄ a))
           → (a : Bool) → Reaches (ann₄ a) (MonParts appop v₃ sp₄ a) (Ok m)
        h₄ (u₄ , v₄ , s₄) shs₄ true  =
          lift (≤<-trans (≤-trans (split3LenL s₄) (split3LenR s₃)) v₂Lt)
        h₄ (u₄ , v₄ , s₄) shs₄ false = tt*

parenGuarded ntm m aPar = p₁
  where
  p₁ : (sp : MonSplit appop m)
     → ((a : Bool) → Sh (par₁ a) (MonParts appop m sp a))
     → (a : Bool) → Reaches (par₁ a) (MonParts appop m sp a) (Ok m)
  p₁ (u , v , s) shs true  = tt*
  p₁ (u , v , s) shs false = p₂
    where
    vLt : length v < length m
    vLt = split3LenR< s (lenLit tlp (shs true))

    p₂ : (sp₂ : MonSplit appop v)
       → ((a : Bool) → Sh (par₂ a) (MonParts appop v sp₂ a))
       → (a : Bool) → Reaches (par₂ a) (MonParts appop v sp₂ a) (Ok m)
    p₂ (u₂ , v₂ , s₂) shs₂ true  = lift (≤<-trans (split3LenL s₂) vLt)
    p₂ (u₂ , v₂ , s₂) shs₂ false = tt*

-- ---- ty ------------------------------------------------------------
parenGuarded nty m yBase = tt*

parenGuarded nty m yArr = k₁
  where
  k₁ : (sp : MonSplit appop m)
     → ((a : Bool) → Sh (arr₁ a) (MonParts appop m sp a))
     → (a : Bool) → Reaches (arr₁ a) (MonParts appop m sp a) (Ok m)
  k₁ (u , v , s) shs true  = tt*
  k₁ (u , v , s) shs false = k₂
    where
    vLt : length v < length m
    vLt = split3LenR< s (lenLit tlp (shs true))

    k₂ : (sp₂ : MonSplit appop v)
       → ((a : Bool) → Sh (arr₂ a) (MonParts appop v sp₂ a))
       → (a : Bool) → Reaches (arr₂ a) (MonParts appop v sp₂ a) (Ok m)
    k₂ (u₂ , v₂ , s₂) shs₂ true  = lift (≤<-trans (split3LenL s₂) vLt)
    k₂ (u₂ , v₂ , s₂) shs₂ false = k₃
      where
      v₂Lt : length v₂ < length m
      v₂Lt = ≤<-trans (split3LenR s₂) vLt

      k₃ : (sp₃ : MonSplit appop v₂)
         → ((a : Bool) → Sh (arr₃ a) (MonParts appop v₂ sp₃ a))
         → (a : Bool) → Reaches (arr₃ a) (MonParts appop v₂ sp₃ a) (Ok m)
      k₃ (u₃ , v₃ , s₃) shs₃ true  = tt*
      k₃ (u₃ , v₃ , s₃) shs₃ false = k₄
        where
        k₄ : (sp₄ : MonSplit appop v₃)
           → ((a : Bool) → Sh (arr₄ a) (MonParts appop v₃ sp₄ a))
           → (a : Bool) → Reaches (arr₄ a) (MonParts appop v₃ sp₄ a) (Ok m)
        k₄ (u₄ , v₄ , s₄) shs₄ true  =
          lift (≤<-trans (≤-trans (split3LenL s₄) (split3LenR s₃)) v₂Lt)
        k₄ (u₄ , v₄ , s₄) shs₄ false = tt*

-- ==================================================================
-- §5  WHAT THE GRAMMAR OWES: the alternatives listed, the constants
-- decided.  Pure inspection.
-- ==================================================================

listedAltT : Listed AltT
listedAltT .elts = aVar ∷ aLam ∷ aApp ∷ aAnn ∷ aPar ∷ []
listedAltT .complete aVar = here
listedAltT .complete aLam = there here
listedAltT .complete aApp = there (there here)
listedAltT .complete aAnn = there (there (there here))
listedAltT .complete aPar = there (there (there (there here)))

listedAltY : Listed AltY
listedAltY .elts = yBase ∷ yArr ∷ []
listedAltY .complete yBase = here
listedAltY .complete yArr  = there here

decEqS : (u v : String) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
decEqS []      []      = inl Eq.refl
decEqS []      (_ ∷ _) = inr λ ()
decEqS (_ ∷ _) []      = inr λ ()
decEqS (a ∷ u) (b ∷ v) = both (decTok a b) (decEqS u v)
  where both : (a Eq.≡ b) ⊎ No (a Eq.≡ b) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
             → ((a ∷ u) Eq.≡ (b ∷ v)) ⊎ No ((a ∷ u) Eq.≡ (b ∷ v))
        both (inl Eq.refl) (inl Eq.refl) = inl Eq.refl
        both (inr k)       _             = inr λ { Eq.refl → k Eq.refl }
        both _             (inr k)       = inr λ { Eq.refl → k Eq.refl }

litProbe : (v : String) → Probe ⌈ v ⌉
litProbe v u _ = decEqS u v

-- PRIMITIVE (phase 1): the two name-carrying constants, by inspection.
decVarTok : (w : String) → VarTok w ⊎ No (VarTok w)
decVarTok []           = inr λ { (n , ()) }
decVarTok (t ∷ ts)     = go t ts
  where
  go : (t : Tok) (ts : String) → VarTok (t ∷ ts) ⊎ No (VarTok (t ∷ ts))
  go (tid n) []      = inl (n , Eq.refl)
  go (tid n) (_ ∷ _) = inr λ { (m , ()) }
  go tlam    _       = inr λ { (m , ()) }
  go tdot    _       = inr λ { (m , ()) }
  go tlp     _       = inr λ { (m , ()) }
  go trp     _       = inr λ { (m , ()) }
  go tcolon  _       = inr λ { (m , ()) }
  go tarrow  _       = inr λ { (m , ()) }
  go tbase   _       = inr λ { (m , ()) }

decBinder : (w : String) → Binder w ⊎ No (Binder w)
decBinder []                              = inr λ { (n , ()) }
decBinder (tlam ∷ tid n ∷ tdot ∷ [])      = inl (n , Eq.refl)
decBinder (tlam ∷ tid n ∷ tdot ∷ _ ∷ _)   = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ tlam   ∷ _)     = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ tlp    ∷ _)     = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ trp    ∷ _)     = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ tcolon ∷ _)     = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ tarrow ∷ _)     = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ tbase  ∷ _)     = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ tid _  ∷ _)     = inr λ { (m , ()) }
decBinder (tlam ∷ tid n ∷ [])             = inr λ { (m , ()) }
decBinder (tlam ∷ tlam   ∷ _)             = inr λ { (m , ()) }
decBinder (tlam ∷ tdot   ∷ _)             = inr λ { (m , ()) }
decBinder (tlam ∷ tlp    ∷ _)             = inr λ { (m , ()) }
decBinder (tlam ∷ trp    ∷ _)             = inr λ { (m , ()) }
decBinder (tlam ∷ tcolon ∷ _)             = inr λ { (m , ()) }
decBinder (tlam ∷ tarrow ∷ _)             = inr λ { (m , ()) }
decBinder (tlam ∷ tbase  ∷ _)             = inr λ { (m , ()) }
decBinder (tlam ∷ [])                     = inr λ { (m , ()) }
decBinder (tid _  ∷ _)                    = inr λ { (m , ()) }
decBinder (tdot   ∷ _)                    = inr λ { (m , ()) }
decBinder (tlp    ∷ _)                    = inr λ { (m , ()) }
decBinder (trp    ∷ _)                    = inr λ { (m , ()) }
decBinder (tcolon ∷ _)                    = inr λ { (m , ()) }
decBinder (tarrow ∷ _)                    = inr λ { (m , ()) }
decBinder (tbase  ∷ _)                    = inr λ { (m , ()) }

parenDec : (x : NT) → DecDesc (parenF x)

parenDec ntm = listedAltT , alt
  where
  alt : (a : AltT) → DecDesc (bodyT a)
  alt aVar = lift λ m _ → decVarTok m
  alt aLam = dLam
    where dLam : (b : Bool) → DecDesc (lamF b)
          dLam true  = lift λ m _ → decBinder m
          dLam false = tt*
  alt aApp = d₁
    where
    d₃ : (b : Bool) → DecDesc (app₃ b)
    d₃ true  = tt*
    d₃ false = lift (litProbe (trp ∷ []))
    d₂ : (b : Bool) → DecDesc (app₂ b)
    d₂ true  = tt*
    d₂ false = d₃
    d₁ : (b : Bool) → DecDesc (app₁ b)
    d₁ true  = lift (litProbe (tlp ∷ []))
    d₁ false = d₂
  alt aAnn = e₁
    where
    e₄ : (b : Bool) → DecDesc (ann₄ b)
    e₄ true  = tt*
    e₄ false = lift (litProbe (trp ∷ []))
    e₃ : (b : Bool) → DecDesc (ann₃ b)
    e₃ true  = lift (litProbe (tcolon ∷ []))
    e₃ false = e₄
    e₂ : (b : Bool) → DecDesc (ann₂ b)
    e₂ true  = tt*
    e₂ false = e₃
    e₁ : (b : Bool) → DecDesc (ann₁ b)
    e₁ true  = lift (litProbe (tlp ∷ []))
    e₁ false = e₂
  alt aPar = p₁
    where
    p₂ : (b : Bool) → DecDesc (par₂ b)
    p₂ true  = tt*
    p₂ false = lift (litProbe (trp ∷ []))
    p₁ : (b : Bool) → DecDesc (par₁ b)
    p₁ true  = lift (litProbe (tlp ∷ []))
    p₁ false = p₂

parenDec nty = listedAltY , alt
  where
  alt : (a : AltY) → DecDesc (bodyY a)
  alt yBase = lift (litProbe (tbase ∷ []))
  alt yArr  = f₁
    where
    f₄ : (b : Bool) → DecDesc (arr₄ b)
    f₄ true  = tt*
    f₄ false = lift (litProbe (trp ∷ []))
    f₃ : (b : Bool) → DecDesc (arr₃ b)
    f₃ true  = lift (litProbe (tarrow ∷ []))
    f₃ false = f₄
    f₂ : (b : Bool) → DecDesc (arr₂ b)
    f₂ true  = tt*
    f₂ false = f₃
    f₁ : (b : Bool) → DecDesc (arr₁ b)
    f₁ true  = lift (litProbe (tlp ∷ []))
    f₁ false = f₂

-- ==================================================================
-- §6  THE PARSER, as a PROBE.  `Dec⟨ Trm ⟩ w` IS `Trm w ⊎ No (Trm w)`,
-- so `decμ` lands in the calculus definitionally.
-- ==================================================================

parseTrm : Probe Trm
parseTrm w _ = decμ parenDec parenGuarded (ntm , w)

parseTy : Probe TyG
parseTy w _ = decμ parenDec parenGuarded (nty , w)
