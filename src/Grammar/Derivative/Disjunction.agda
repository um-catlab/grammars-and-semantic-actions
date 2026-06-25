open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Derivative.Disjunction (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary.Base using (Discrete; Dec; yes; no)
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Top Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Function Alphabet
open import Grammar.Negation Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.Distributivity Alphabet
open import Grammar.String Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

open StrongEquivalence

private
  variable
    w v : String
    ℓ ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB
    X : Grammar ℓ

------------------------------------------------------------------------------
-- An alternative encoding of the string-indexed "amazing right adjoint" √l.
--
-- The exponential encoding (Grammar.Derivative.String) is
--     √l-string w A = (⌈ w ⌉ ⊗ ⊤) ⇒ (⌈ w ⌉ ⊗ A).
-- Using a parse only ever requires *triggering* the domain `⌈ w ⌉ ⊗ ⊤`, and
-- `⌈ w ⌉ ⊗ ⊤` ("does the string start with w?") is DECIDABLE.  So we can split
-- on it up front and replace the exponential by a SUM:
--
--     √w A  :=  (⌈ w ⌉ ⊗ A)  ⊕  ¬(⌈ w ⌉ ⊗ ⊤)
--
-- i.e. "either the string starts with w and carries an A on the residual, or it
-- does not start with w at all".  The decidability witness
--     ⊤ ⊢ (⌈ w ⌉ ⊗ ⊤) ⊕ ¬(⌈ w ⌉ ⊗ ⊤)
-- lets us always inspect which case we are in — the move the exponential's
-- application used to do implicitly.  The pay-off: the functor action, counit,
-- and comultiplication become plain sum/product manipulations (no `transport`
-- gymnastics over index paths, which dominated the exponential proofs).
------------------------------------------------------------------------------

-- "the string starts with w"
Start : String → Grammar ℓ-zero
Start w = ⌈ w ⌉ ⊗ ⊤

-- "the string does NOT start with w"
¬Start : String → Grammar ℓ-zero
¬Start w = ¬G Start w

-- The disjunctive √l.
√l-string : String → Grammar ℓA → Grammar ℓA
√l-string w A = (⌈ w ⌉ ⊗ A) ⊕ ¬Start w

------------------------------------------------------------------------------
-- Functor action  (a one-liner: relabel the carried A on the prefix branch)
------------------------------------------------------------------------------

√l-map : A ⊢ B → √l-string w A ⊢ √l-string w B
√l-map f = ⊕-elim (inl ∘g (id ,⊗ f)) inr

------------------------------------------------------------------------------
-- Counit  √l-string [] A ≅ A    (⌈ [] ⌉ = ε, and ¬Start [] is uninhabited)
------------------------------------------------------------------------------

-- ¬Start [] is absurd: every string starts with the empty prefix, so the
-- negation can be fed its own always-present witness `ε ⊗ ⊤`.
¬Start[]→⊥ : ¬Start [] ⊢ ⊥
¬Start[]→⊥ = ⇒-app ∘g &-intro id (⊗-unit-l⁻ ∘g ⊤-intro)

√l-ε : √l-string [] A ⊢ A
√l-ε = ⊕-elim ⊗-unit-l (⊥-elim ∘g ¬Start[]→⊥)

√l-ε⁻ : A ⊢ √l-string [] A
√l-ε⁻ = inl ∘g ⊗-unit-l⁻

------------------------------------------------------------------------------
-- Splitting a concatenated prefix grammar (used by √l-cat's prefix branch)
------------------------------------------------------------------------------

⌈⌉-split : ∀ w v → ⌈ w ++ v ⌉ ⊢ ⌈ w ⌉ ⊗ ⌈ v ⌉
⌈⌉-split [] v = ⊗-unit-l⁻
⌈⌉-split (c ∷ w) v = ⊗-assoc ∘g (id ,⊗ ⌈⌉-split w v)

------------------------------------------------------------------------------
-- Small pointwise lemmas about prefixes (`ε`, `literal` are `Eq.≡`-based).
------------------------------------------------------------------------------

private
  nil≢cons : ∀ {x : ⟨ Alphabet ⟩} {xs} → [] Eq.≡ x ∷ xs → Empty.⊥
  nil≢cons p = Eq.transport (λ { [] → Unit ; (_ ∷ _) → Empty.⊥ }) p tt

opaque
  unfolding _⊗_ _&_ _⇒_ ⊤ ⊥ ε literal

  -- empty string does not start with `c ∷ …`
  ¬first : ∀ {c} → ε ⊢ ¬G (＂ c ＂ ⊗ X)
  ¬first {c = c} u eu ((( l , r ) , pf) , (litc , _)) =
    nil≢cons (Eq.sym eu Eq.∙ pf Eq.∙ Eq.ap (_++ r) litc)

  -- starts with c, but the residual is NOT in X  ⟹  not (c then X)
  c⊗¬X→¬cX : ∀ {c} → ＂ c ＂ ⊗ ¬G X ⊢ ¬G (＂ c ＂ ⊗ X)
  c⊗¬X→¬cX {X = X} {c = c} u
    ((( l , r ) , pf) , (litc , neg)) ((( l' , r' ) , pf') , (litc' , x)) =
    neg (Eq.transport X (Eq.sym r≡r') x)
    where
      r≡r' : r Eq.≡ r'
      r≡r' = ++-cancelˡEq (c ∷ [])
        ( Eq.ap (_++ r) (Eq.sym litc)
          Eq.∙ Eq.sym pf Eq.∙ pf'
          Eq.∙ Eq.ap (_++ r') litc' )

  -- two distinct leading characters cannot both head the same string
  firstChar-disjoint : ∀ {c c'} → (c ≡ c' → Empty.⊥)
    → (＂ c ＂ ⊗ ⊤) & (＂ c' ＂ ⊗ ⊤) ⊢ ⊥
  firstChar-disjoint {c = c} {c' = c'} c≢c' u
    (((( l , r ) , pf) , (litc , _)) , ((( l' , r' ) , pf') , (litc' , _))) =
    c≢c' (Eq.eqToPath c≡c')
    where
      c≡c' : c Eq.≡ c'
      c≡c' = Eq.ap (λ { [] → c ; (x ∷ _) → x })
        ( Eq.ap (_++ r) (Eq.sym litc)
          Eq.∙ Eq.sym pf Eq.∙ pf'
          Eq.∙ Eq.ap (_++ r') litc' )

  -- starts with w but NOT with w ++ v  ⟹  the w-residual does not start with v
  -- (recombine ⌈ w ⌉ ⊗ ⌈ v ⌉ into ⌈ w ++ v ⌉ to contradict ¬Start (w ++ v)).
  Start&¬Start-cat : ∀ w v → Start w & ¬Start (w ++ v) ⊢ ⌈ w ⌉ ⊗ ¬Start v
  Start&¬Start-cat w v u (sw , neg) =
    sw .fst , (sw .snd .fst , negv)
    where
      lw rw : String
      lw = sw .fst .fst .fst
      rw = sw .fst .fst .snd

      negv : ¬Start v rw
      negv ((( lv , rv ) , pfv) , (⌈v⌉lv , _)) = neg start[w++v]
        where
          ⌈wv⌉ : ⌈ w ++ v ⌉ (lw ++ lv)
          ⌈wv⌉ = ⌈⌉-++ w v (lw ++ lv)
            ((( lw , lv ) , Eq.refl) , (sw .snd .fst , ⌈v⌉lv))

          start[w++v] : Start (w ++ v) u
          start[w++v] =
            ((( lw ++ lv , rv )
              , ( sw .fst .snd
                  Eq.∙ Eq.ap (lw ++_) pfv
                  Eq.∙ Eq.sym (++-assoc-Eq lw lv rv) ))
            , (⌈wv⌉ , _))

------------------------------------------------------------------------------
-- The single genuine obligation of this encoding: DECIDABILITY of `Start w`.
-- (Needs decidable equality on the alphabet to compare the leading character.)
------------------------------------------------------------------------------

module _ (disc : Discrete ⟨ Alphabet ⟩) where

  -- Decide `＂ c ＂ ⊗ X` from a decision for `X`, by peeking the first character.
  dec-cons : ∀ {c} → ⊤ ⊢ X ⊕ ¬G X → ⊤ ⊢ (＂ c ＂ ⊗ X) ⊕ ¬G (＂ c ＂ ⊗ X)
  dec-cons {X = X} {c = c} decX =
    ⊕-elim
      (inr ∘g ¬first ∘g π₂)                 -- (⊤ & ε): empty, no leading c
      (⊕ᴰ-elim branch)                      -- ⊕[c'] (⊤ & startsWith c')
    ∘g firstChar≅ .fun
    where
      target : Grammar _
      target = (＂ c ＂ ⊗ X) ⊕ ¬G (＂ c ＂ ⊗ X)

      -- when the actual leading character equals c: recurse on the residual.
      branchEq : (⊤ & startsWith c) ⊢ target
      branchEq =
        ⊕-elim inl (inr ∘g c⊗¬X→¬cX)
        ∘g ⊗⊕-distL
        ∘g (id ,⊗ (decX ∘g ⊤-intro))
        ∘g π₂

      branch : ∀ c' → (⊤ & startsWith c') ⊢ target
      branch c' with disc c c'
      ... | yes c≡c' =
        subst (λ z → (⊤ & startsWith z) ⊢ target) c≡c' branchEq
      ... | no  c≢c' =
        inr ∘g ⇒-intro
          ( firstChar-disjoint c≢c'
            ∘g &-intro ((id ,⊗ ⊤-intro) ∘g π₂)
                       ((id ,⊗ ⊤-intro) ∘g π₂ ∘g π₁) )

  -- ⊤ ⊢ Start w ⊕ ¬Start w  — decide whether the string starts with w.
  dec-Start : ∀ w → ⊤ ⊢ Start w ⊕ ¬Start w
  dec-Start []      = inl ∘g ⊗-unit-l⁻
  dec-Start (c ∷ w) =
    (⊗-assoc ,⊕p ⇒-mapDom ⊗-assoc⁻) ∘g dec-cons {c = c} (dec-Start w)

  ------------------------------------------------------------------------------
  -- Comultiplication  √l-cat : √(w ++ v) A ⊢ √w (√v A)
  --
  -- Compare with the exponential `√l-cat`/`√l-cat-εr`/pentagon, which needed
  -- nested `Eq.transport`s over `++`-paths.  Here it is sum-elimination:
  --   • prefix branch  (⌈ w++v ⌉ ⊗ A): split the prefix, reassociate, `inl`.
  --   • no-prefix branch (¬Start (w++v)): DECIDE `Start w`.
  --       – starts with w but not w++v  ⟹  ¬Start v   (Start&¬Start-cat)
  --       – does not start with w       ⟹  ¬Start w   directly.
  ------------------------------------------------------------------------------
  √l-cat : ∀ {w v} → √l-string (w ++ v) A ⊢ √l-string w (√l-string v A)
  √l-cat {A = A} {w = w} {v = v} = ⊕-elim prefix-branch noprefix-branch
    where
      prefix-branch : ⌈ w ++ v ⌉ ⊗ A ⊢ √l-string w (√l-string v A)
      prefix-branch =
        inl ∘g (id ,⊗ inl) ∘g ⊗-assoc⁻ ∘g (⌈⌉-split w v ,⊗ id)

      noprefix-branch : ¬Start (w ++ v) ⊢ √l-string w (√l-string v A)
      noprefix-branch =
        ⊕-elim
          (inl ∘g (id ,⊗ inr) ∘g Start&¬Start-cat w v)
          (inr ∘g π₁)
        ∘g &⊕-distR
        ∘g &-intro (dec-Start w ∘g ⊤-intro) id
