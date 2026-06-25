{-
  Reflect: consequences of the Yoneda-slice primitive (Grammar.Yoneda.Base).

  The point of this module is to rebuild the facts that the (now-deleted)
  Grammar.External.LinearProduct.SplittingTrichotomy used to establish by
  hand (Splitting surgery + subst/Eq.transport), but as corollaries of the
  Yoneda-slice keystone (Grammar.Yoneda.Base.slice≅).  `⊗&-distL≅` here is
  what Grammar.SequentialUnambiguity.Base now uses; the 775-line trichotomy
  file has been retired.  (Grammar.External.String.Tiny still survives for
  its other consumers: Box, Greedy, Later, Unfold, Parser.)
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Yoneda.Reflect (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; ++-unit-r)
open import Cubical.Data.List.Properties using (Split++ ; split++ ; ¬cons≡nil)
import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Yoneda.Base Alphabet
open import Grammar.SequentialUnambiguity.First Alphabet
open import Grammar.SequentialUnambiguity.FollowLast Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC : Level
    w : String
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC

open StrongEquivalence

-- ⊗-reflect: an (A ⊗ B)-parse of a *named* string w is exactly a
-- splitting of w (honest `SplittingEq w` data) together with an
-- A-parse of the left piece and a B-parse of the right piece -- all
-- tagged onto the canonical ⌈ w ⌉ witness.  No surgery: this is just
-- `slice≅` specialised, with the index `(A ⊗ B) w` left to unfold to
-- the Day-convolution Σ on demand.
⊗-reflect : ((A ⊗ B) & ⌈ w ⌉) ≅ (⊕[ _ ∈ (A ⊗ B) w ] ⌈ w ⌉)
⊗-reflect {A = A} {B = B} {w = w} = slice≅ (A ⊗ B) w

-- Representable-pinned merge: a `⌈ w ⌉` prefix (here reached from P via
-- P→⌈⌉) fixes the split point, so the two ⊗-splits coincide and the right
-- factors merge.  No Levi / no ⊛: `uniquely-supported-⌈⌉Eq` (the Yoneda
-- extraction) pins both left pieces to `w`, then ++-cancelˡEq fixes the
-- suffix.  Replaces Grammar.External.String.Tiny.⌈⌉-prefix-push.
opaque
  unfolding _⊗_ _&_
  ⌈⌉-prefix-push : ∀ {w} {P : Grammar ℓA} {Q : Grammar ℓB} {R : Grammar ℓC}
    → (P ⊢ ⌈ w ⌉)
    → (P ⊗ Q) & (⌈ w ⌉ ⊗ R) ⊢ P ⊗ (Q & R)
  ⌈⌉-prefix-push {w = w} {R = R} P→⌈⌉ v ((s , p , q) , (s' , p' , q')) =
    s , p , q , Eq.transport R rs'≡rs q'
    where
    w≡ls : w Eq.≡ s .fst .fst
    w≡ls = uniquely-supported-⌈⌉Eq w (s .fst .fst) (P→⌈⌉ (s .fst .fst) p)
    w≡ls' : w Eq.≡ s' .fst .fst
    w≡ls' = uniquely-supported-⌈⌉Eq w (s' .fst .fst) p'
    ls≡ls' : s .fst .fst Eq.≡ s' .fst .fst
    ls≡ls' = Eq.sym w≡ls Eq.∙ w≡ls'
    chain : s .fst .fst ++ s' .fst .snd Eq.≡ s .fst .fst ++ s .fst .snd
    chain = Eq.ap (_++ s' .fst .snd) ls≡ls' Eq.∙ Eq.sym (s' .snd) Eq.∙ s .snd
    rs'≡rs : s' .fst .snd Eq.≡ s .fst .snd
    rs'≡rs = ++-cancelˡEq (s .fst .fst) chain

-- Sequential unambiguity, defined directly on the clean First/FollowLast
-- predicates (no dependency on SplittingTrichotomy / Tiny).
sequentiallyUnambiguous : Grammar ℓA → Grammar ℓB → Type (ℓ-max ℓA ℓB)
sequentiallyUnambiguous A B =
  ∀ (c : ⟨ Alphabet ⟩) → ⟨ c ∉FollowLast A ⟩ ⊎ ⟨ c ∉First B ⟩

syntax sequentiallyUnambiguous A B = A ⊛ B

-- The workhorse the SplittingTrichotomy file exists to support.
-- Target: prove it from `slice≅` instead of the hand-rolled trichotomy.
--
-- inv direction is trivial.  The fun direction is the whole content:
-- slice both factors by the parsed string (density), `⊗-reflect` each to
-- expose the two splittings of one `w`, classify the pair with the
-- existing list lemma `Split++` (Levi / equidivisibility), and kill the
-- two off-diagonal (prefix) cases with the `⊛` hypotheses --
-- the interpolant's first character would land in both
-- `FollowLast A` and `First B` (resp. C), contradiction.
module _ (A : Grammar ℓA) (B : Grammar ℓB) (C : Grammar ℓC)
  (A⊛B : A ⊛ B) (A⊛C : A ⊛ C)
  where

  opaque
    unfolding _&_ _⊗_ ⊥
    ⊗&-distL-inv : ((A & A) ⊗ (B & C)) ⊢ ((A ⊗ B) & (A ⊗ C))
    ⊗&-distL-inv w (t , (a1 , a2) , (b , c)) = ((t , a1 , b) , (t , a2 , c))

    ⊗&-distL-fun : ((A ⊗ B) & (A ⊗ C)) ⊢ ((A & A) ⊗ (B & C))
    ⊗&-distL-fun w ((s , a , b) , (s' , a' , c))
      with split++ (s .fst .fst) (s .fst .snd) (s' .fst .fst) (s' .fst .snd)
             (sym (Eq.eqToPath (s .snd)) ∙ Eq.eqToPath (s' .snd))
    -- diagonal: the two splits coincide -> merge into (A & A) ⊗ (B & C)
    ... | ([]     , Sum.inl (e1 , e2)) =
      s , ( (a , subst A (sym e1 ∙ ++-unit-r (s .fst .fst)) a')
          , (b , subst C (sym e2) c) )
    ... | ([]     , Sum.inr (e1 , e2)) =
      s , ( (a , subst A (sym (++-unit-r (s' .fst .fst)) ∙ e1) a')
          , (b , subst C e2 c) )
    -- off-diagonal: nonempty interpolant g ∷ zs.  g would sit in both
    -- FollowLast A and First B (resp. C); killed by A⊛B (resp. A⊛C).
    -- inl: ls ⊊ ls' = ls ++ (g ∷ zs); g follows the A-parse `a` and starts `b`.
    ... | (g ∷ zs , Sum.inl (e1 , e2)) =
      Sum.rec
        (λ g∉FLA → Empty.rec
          (g∉FLA (s .fst .fst ++ (g ∷ zs))
            ( ⊗-mk (splittingEq++ (s .fst .fst) (g ∷ zs)) a
                (⊗-mk (splittingEq++ (g ∷ []) zs) lit-intro (mkstring zs))
            , subst A (sym e1) a' )))
        (λ g∉FB → Empty.rec
          (g∉FB ((g ∷ zs) ++ s' .fst .snd)
            ( ⊗-mk (splittingEq++ (g ∷ []) (zs ++ s' .fst .snd))
                lit-intro (mkstring (zs ++ s' .fst .snd))
            , subst B e2 b )))
        (A⊛B g)
    -- inr: ls' ⊊ ls = ls' ++ (g ∷ zs); g follows `a'` and starts `c`.
    ... | (g ∷ zs , Sum.inr (e1 , e2)) =
      Sum.rec
        (λ g∉FLA → Empty.rec
          (g∉FLA (s' .fst .fst ++ (g ∷ zs))
            ( ⊗-mk (splittingEq++ (s' .fst .fst) (g ∷ zs)) a'
                (⊗-mk (splittingEq++ (g ∷ []) zs) lit-intro (mkstring zs))
            , subst A (sym e1) a )))
        (λ g∉FC → Empty.rec
          (g∉FC ((g ∷ zs) ++ s .fst .snd)
            ( ⊗-mk (splittingEq++ (g ∷ []) (zs ++ s .fst .snd))
                lit-intro (mkstring (zs ++ s .fst .snd))
            , subst C e2 c )))
        (A⊛C g)

    -- ret: inv ∘ fun ≡ id.  Diagonal cases recover the original splitting
    -- (SplittingEq≡) and parses (transport-filler); off-diagonal cases are
    -- the same ⊛-contradiction, now discharged into the Path goal.
    theRet : ∀ w (x : ((A ⊗ B) & (A ⊗ C)) w)
      → ⊗&-distL-inv w (⊗&-distL-fun w x) ≡ x
    theRet w ((s , a , b) , (s' , a' , c))
      with split++ (s .fst .fst) (s .fst .snd) (s' .fst .fst) (s' .fst .snd)
             (sym (Eq.eqToPath (s .snd)) ∙ Eq.eqToPath (s' .snd))
    ... | ([]     , Sum.inl (e1 , e2)) =
      ΣPathP (refl ,
        ΣPathP (SplittingEq≡ (≡-× (sym (sym e1 ∙ ++-unit-r (s .fst .fst))) e2) ,
          ΣPathP ( symP (transport-filler (λ i → A ((sym e1 ∙ ++-unit-r (s .fst .fst)) i)) a')
                 , symP (transport-filler (λ i → C ((sym e2) i)) c) )))
    ... | ([]     , Sum.inr (e1 , e2)) =
      ΣPathP (refl ,
        ΣPathP (SplittingEq≡ (≡-× (sym (sym (++-unit-r (s' .fst .fst)) ∙ e1)) (sym e2)) ,
          ΣPathP ( symP (transport-filler (λ i → A ((sym (++-unit-r (s' .fst .fst)) ∙ e1) i)) a')
                 , symP (transport-filler (λ i → C (e2 i)) c) )))
    ... | (g ∷ zs , Sum.inl (e1 , e2)) =
      Sum.rec
        (λ g∉FLA → Empty.rec
          (g∉FLA (s .fst .fst ++ (g ∷ zs))
            ( ⊗-mk (splittingEq++ (s .fst .fst) (g ∷ zs)) a
                (⊗-mk (splittingEq++ (g ∷ []) zs) lit-intro (mkstring zs))
            , subst A (sym e1) a' )))
        (λ g∉FB → Empty.rec
          (g∉FB ((g ∷ zs) ++ s' .fst .snd)
            ( ⊗-mk (splittingEq++ (g ∷ []) (zs ++ s' .fst .snd))
                lit-intro (mkstring (zs ++ s' .fst .snd))
            , subst B e2 b )))
        (A⊛B g)
    ... | (g ∷ zs , Sum.inr (e1 , e2)) =
      Sum.rec
        (λ g∉FLA → Empty.rec
          (g∉FLA (s' .fst .fst ++ (g ∷ zs))
            ( ⊗-mk (splittingEq++ (s' .fst .fst) (g ∷ zs)) a'
                (⊗-mk (splittingEq++ (g ∷ []) zs) lit-intro (mkstring zs))
            , subst A (sym e1) a )))
        (λ g∉FC → Empty.rec
          (g∉FC ((g ∷ zs) ++ s .fst .snd)
            ( ⊗-mk (splittingEq++ (g ∷ []) (zs ++ s .fst .snd))
                lit-intro (mkstring (zs ++ s .fst .snd))
            , subst C e2 c )))
        (A⊛C g)

    -- sec: fun ∘ inv ≡ id.  Here both input splittings are the same `t`, so
    -- only the diagonal cases arise; the merge's transports are along
    -- String-loops, killed by isSetString.  Off-diagonal is absurd.
    theSec : ∀ w (y : ((A & A) ⊗ (B & C)) w)
      → ⊗&-distL-fun w (⊗&-distL-inv w y) ≡ y
    theSec w (t , (a1 , a2) , (b , c))
      with split++ (t .fst .fst) (t .fst .snd) (t .fst .fst) (t .fst .snd)
             (sym (Eq.eqToPath (t .snd)) ∙ Eq.eqToPath (t .snd))
    ... | ([]     , Sum.inl (e1 , e2)) =
      ΣPathP (refl ,
        ΣPathP ( ΣPathP (refl ,
                   cong (λ p → subst A p a2)
                     (isSetString _ _ (sym e1 ∙ ++-unit-r (t .fst .fst)) refl)
                   ∙ substRefl {B = A} a2)
               , ΣPathP (refl ,
                   cong (λ p → subst C p c) (isSetString _ _ (sym e2) refl)
                   ∙ substRefl {B = C} c) ))
    ... | ([]     , Sum.inr (e1 , e2)) =
      ΣPathP (refl ,
        ΣPathP ( ΣPathP (refl ,
                   cong (λ p → subst A p a2)
                     (isSetString _ _ (sym (++-unit-r (t .fst .fst)) ∙ e1) refl)
                   ∙ substRefl {B = A} a2)
               , ΣPathP (refl ,
                   cong (λ p → subst C p c) (isSetString _ _ e2 refl)
                   ∙ substRefl {B = C} c) ))
    ... | (g ∷ zs , Sum.inl (e1 , e2)) =
      Empty.rec (¬cons≡nil (++unit→[] (t .fst .fst) (g ∷ zs) e1))
    ... | (g ∷ zs , Sum.inr (e1 , e2)) =
      Empty.rec (¬cons≡nil (++unit→[] (t .fst .fst) (g ∷ zs) e1))

  ⊗&-distL≅ : ((A ⊗ B) & (A ⊗ C)) ≅ ((A & A) ⊗ (B & C))
  ⊗&-distL≅ .fun = ⊗&-distL-fun
  ⊗&-distL≅ .inv = ⊗&-distL-inv
  ⊗&-distL≅ .sec = funExt λ w → funExt (theSec w)
  ⊗&-distL≅ .ret = funExt λ w → funExt (theRet w)
