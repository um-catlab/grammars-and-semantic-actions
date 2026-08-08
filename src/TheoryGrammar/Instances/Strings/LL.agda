{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- AN LL(1) GRAMMAR AND ITS LOOKAHEAD AUTOMATON. S → 'a' S 'b' | 'c' (the
   language aⁿ c bⁿ) Two alternatives with disjoint FIRST sets -- {a} and
   {c} -- so one symbol of lookahead determines the production. -}
module TheoryGrammar.Instances.Strings.LL where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed
open import TheoryGrammar.Decidable.Lookahead
open import TheoryGrammar.SemanticAction

-- §0  The alphabet.

data Chr : Type₀ where ca cb cc : Chr

decEqChr : (x y : Chr) → (x Eq.≡ y) ⊎ No (x Eq.≡ y)
decEqChr ca ca = inl Eq.refl
decEqChr cb cb = inl Eq.refl
decEqChr cc cc = inl Eq.refl
decEqChr ca cb = inr λ ()
decEqChr ca cc = inr λ ()
decEqChr cb ca = inr λ ()
decEqChr cb cc = inr λ ()
decEqChr cc ca = inr λ ()
decEqChr cc cb = inr λ ()

open import TheoryGrammar.Instances.Strings.Enumeration Chr

-- PRIMITIVE (phase 1). External decidability of the carrier -- the one
-- entry point `Decidable.Representable` sanctions, and the only place in
-- this file where an `inl`/`inr` is matched by hand.
decEqS : (u v : String) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
decEqS []      []      = inl Eq.refl
decEqS []      (_ ∷ _) = inr λ ()
decEqS (_ ∷ _) []      = inr λ ()
decEqS (a ∷ u) (b ∷ v) = both (decEqChr a b) (decEqS u v)
  where both : _ → _ → ((a ∷ u) Eq.≡ (b ∷ v)) ⊎ No ((a ∷ u) Eq.≡ (b ∷ v))
        both (inl Eq.refl) (inl Eq.refl) = inl Eq.refl
        both (inr k)       _             = inr λ { Eq.refl → k Eq.refl }
        both _             (inr k)       = inr λ { Eq.refl → k Eq.refl }

enumSplitL : (o : MonOp) (m : String) → Listed (MonSplit o m)
enumSplitL o m .elts     = enumSplit o m
enumSplitL o m .complete = enumComplete o m

enumArL : (o : MonOp) → Listed (MonAr o)
enumArL nilop .elts     = []
enumArL nilop .complete = λ ()
enumArL appop .elts     = true ∷ false ∷ []
enumArL appop .complete true  = here
enumArL appop .complete false = there here

-- ... and re-read as an internal PROBE, which is the form
-- `Representable` calls for: decidability of a sort IS decidability of
-- `⌈_⌉`.  `decEqS` is the witness; `litProbe` is the primitive.
litProbe : (v : String) → Probe ⌈ v ⌉
litProbe v u _ = decEqS u v

open Look strGraded ℓ-zero Unit (λ _ → tt) enumSplitL enumArL
  using ( Alts ; Alt ; body ; descOf ; Lookahead ; St ; look ; sel ; sound
        ; DecDesc ; GuardedD ; Reaches ; Layer⁺ ; Layerᴳ ; LookAt
        ; decLL ; toSelᴳ ; fromSelᴳ ; lookTotal )

-- §1  The grammar, in alternatives form.

litA litB litC : Gr
litA = ⌈ ca ∷ [] ⌉
litB = ⌈ cb ∷ [] ⌉
litC = ⌈ cc ∷ [] ⌉

-- S ⊗ 'b'
rhs₂ : Bool → Functor tt
rhs₂ true  = Var tt
rhs₂ false = ⌜ litB ⌝

-- 'a' ⊗ (S ⊗ 'b')
rhs₁ : Bool → Functor tt
rhs₁ true  = ⌜ litA ⌝
rhs₁ false = ⊗e appop rhs₂

sAlts : Alts
sAlts .Alt  _     = Bool
sAlts .body _ true  = ⊗e appop rhs₁      -- S → 'a' S 'b'
sAlts .body _ false = ⌜ litC ⌝           -- S → 'c'

S : Gr
S w = μ (descOf sAlts) (tt , w)

-- §2  THE LOOKAHEAD AUTOMATON, and it computes.

headMay : String → Maybe Chr
headMay []      = nothing
headMay (c ∷ _) = just c

pick : Maybe Chr → Bool
pick (just ca) = true       -- FIRST(S → 'a' S 'b') = {a}
pick _         = false      -- FIRST(S → 'c')       = {c}

-- the automaton, run.  These are the lookahead table's entries.
_ : headMay (ca ∷ cc ∷ cb ∷ []) ≡ just ca
_ = refl

_ : pick (headMay (ca ∷ cc ∷ cb ∷ [])) ≡ true
_ = refl

_ : pick (headMay (cc ∷ [])) ≡ false
_ = refl

_ : pick (headMay []) ≡ false
_ = refl

-- §3  SOUNDNESS -- i.e. the grammar really is LL(1).

-- INTERNAL: a `⊢`-term between fixed grammars.
soundLL : (x : Unit) (a : Bool) (st : Maybe Chr)
        → (Layerᴳ sAlts (sAlts .body x a) & LookAt (λ _ → headMay) st)
          ⊢ Layerᴳ sAlts (sAlts .body x (pick st))
-- the base production pins the world outright, hence pins the state
soundLL tt false .(just cc) .(cc ∷ []) ((lift Eq.refl , f) , Eq.refl) =
  lift Eq.refl , f
-- the recursive production exhibits a splitting whose LEFT FACTOR IS 'a',
-- so the world is `ca ∷ _`, the state is `just ca`, and `pick` REDUCES
soundLL tt true st m ((((u , v , s) , shs) , f) , lk) with lower (shs true)
soundLL tt true .(just ca) .(ca ∷ v)
        ((((.(ca ∷ []) , v , cons nil) , shs) , f) , Eq.refl) | Eq.refl =
  (((ca ∷ [] , v , cons nil) , shs) , f)

-- §4  The remaining obligations, per alternative.

sLook : Lookahead sAlts
sLook .St       = Maybe Chr
sLook .look _   = headMay
sLook .sel  _   = pick
sLook .sound    = soundLL

sDec : (x : Unit) (a : Bool) → DecDesc (sAlts .body x a)
sDec tt false = lift (litProbe (cc ∷ []))
sDec tt true  = d₁
  where
    d₂ : (b : Bool) → DecDesc (rhs₂ b)
    d₂ true  = tt*
    d₂ false = lift (litProbe (cb ∷ []))

    d₁ : (b : Bool) → DecDesc (rhs₁ b)
    d₁ true  = lift (litProbe (ca ∷ []))
    d₁ false = d₂

private
  Ok : String → Ix → Type₀
  Ok m j = degIx j < length m

  lenA : {u : String} → Sh (⌜ litA ⌝) u → 0 < length u
  lenA sh = go (lower sh)
    where go : {u : String} → u Eq.≡ (ca ∷ []) → 0 < length u
          go Eq.refl = ≤-refl

sGuard : (x : Unit) (a : Bool) (m : String) → GuardedD (sAlts .body x a) m
sGuard tt false m = tt*
sGuard tt true  m = outer
  where
    outer : (sp : MonSplit appop m)
          → ((b : Bool) → Sh (rhs₁ b) (MonParts appop m sp b))
          → (b : Bool) → Reaches (rhs₁ b) (MonParts appop m sp b) (Ok m)
    outer (u , v , s) shs true  = tt*
    outer (u , v , s) shs false = mid
      where
        vLt : length v < length m
        vLt = split3LenR< s (lenA (shs true))

        mid : (sp₂ : MonSplit appop v)
            → ((b : Bool) → Sh (rhs₂ b) (MonParts appop v sp₂ b))
            → (b : Bool) → Reaches (rhs₂ b) (MonParts appop v sp₂ b) (Ok m)
        mid (u₂ , v₂ , s₂) shs₂ true  = lift (≤<-trans (split3LenL s₂) vLt)
        mid (u₂ , v₂ , s₂) shs₂ false = tt*

-- §5 THE PARSER, as a PROBE. This one line is the only place the
-- metalanguage `⊎` appears -- `Dec⟨ S ⟩ w` IS `S w ⊎ No (S w)`, so `decLL`
-- lands in the calculus definitionally.

sProbe : Probe S
sProbe w _ = decLL sLook sDec sGuard (tt , w)

-- §6 THE PARSE TREE, by a SEMANTIC ACTION. wrapT t reads "a t b", leafT
-- reads "c" so the tree of `aⁿ c bⁿ` is `wrapT^n leafT` -- the
-- derivation's depth is the input's nesting, which is what a Boolean
-- throws away.

data Tree : Type₀ where
  leafT : Tree
  wrapT : Tree → Tree

module AI = ActInd strFib ℓ-zero Unit (λ _ → tt)

TreeMot : Ix → Type₀
TreeMot i = Δ Tree (i .snd)

sAlg : AI.ActAlg (descOf sAlts) (λ _ → Tree)
sAlg tt = ⊕ᴰ-E branch
  where
    -- S ⊗ 'b'  --  keep the subtree, drop the literal
    lvl₂ : ⟦ ⊗e appop rhs₂ ⟧c TreeMot ⊢ Δ Tree
    lvl₂ = mapA (λ f → f true)
           (⊗A appop {A = λ b → ⟦ rhs₂ b ⟧c TreeMot} (λ _ → Tree)
               (λ { true → idA ; false → pureA Tree leafT }))

    -- 'a' ⊗ (S ⊗ 'b')  --  drop the literal
    lvl₁ : ⟦ ⊗e appop rhs₁ ⟧c TreeMot ⊢ Δ Tree
    lvl₁ = mapA (λ f → f false)
           (⊗A appop {A = λ b → ⟦ rhs₁ b ⟧c TreeMot} (λ _ → Tree)
               (λ { true → pureA Tree leafT ; false → lvl₂ }))

    branch : (a : Bool) → ⟦ sAlts .body tt a ⟧c TreeMot ⊢ Δ Tree
    branch false = pureA Tree leafT
    branch true  = mapA wrapT lvl₁

readTree : S ⊢ Δ Tree
readTree = AI.recA sAlg tt

-- the pipeline: the action runs on the success branch, the refutation is
-- left alone
parse! : ⊤G ⊢ Δ (Maybe Tree)
parse! = maybeA S (¬G S) readTree ∘g sProbe

-- the Boolean shadow, same observer at a different error grammar
accepts! : ⊤G ⊢ Δ Bool
accepts! = okA S (¬G S) ∘g sProbe

-- §7  THE TREES, pinned.

_ : passes (run parse! at
             ( (cc ∷ [])                         ↦ just leafT
             ∷ (ca ∷ cc ∷ cb ∷ [])               ↦ just (wrapT leafT)
             ∷ (ca ∷ ca ∷ cc ∷ cb ∷ cb ∷ [])     ↦ just (wrapT (wrapT leafT))
             ∷ [] ))
_ = refl

_ : passes (run parse! at
             ( []                                ↦ nothing
             ∷ (ca ∷ cc ∷ [])                    ↦ nothing   -- missing b
             ∷ (ca ∷ cb ∷ [])                    ↦ nothing   -- missing c
             ∷ (ca ∷ ca ∷ cc ∷ cb ∷ [])          ↦ nothing   -- unbalanced
             ∷ (cb ∷ cc ∷ ca ∷ [])               ↦ nothing
             ∷ [] ))
_ = refl

-- §8  STRESS.  `word n` is `aⁿ c bⁿ`, whose tree is `wrapT^n leafT`, so
-- the expected answer is generated rather than written out -- a test
-- that scales with the input.

reps : ℕ → Chr → String
reps zero    c = []
reps (suc n) c = c ∷ reps n c

word : ℕ → String
word n = reps n ca ++ (cc ∷ reps n cb)

wraps : ℕ → Tree
wraps zero    = leafT
wraps (suc n) = wrapT (wraps n)

_ : passes (run parse! at ( word 1 ↦ just (wraps 1)
                          ∷ word 2 ↦ just (wraps 2)
                          ∷ word 3 ↦ just (wraps 3)
                          ∷ [] ))
_ = refl
