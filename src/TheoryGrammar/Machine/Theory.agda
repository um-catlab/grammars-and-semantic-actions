{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE ISA `Fibered`, AND HOARE LOGIC AS ITS CONNECTIVES. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt; Unit*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

module TheoryGrammar.Machine.Theory
  (Fib  : Fibered monoidSig ℓ-zero ℓ-zero)     -- machine resource
  (PFib : Fibered monoidSig ℓ-zero ℓ-zero)     -- program text
  (Run  : PFib .carrier tt → Fib .carrier tt → Fib .carrier tt → Type₀)
  where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.RulesFib
open import TheoryGrammar.Machine.Signature

private variable ℓA ℓB ℓC : Level

-- The carriers.

Res : Type₀
Res = Fib .carrier tt

Prog : Type₀
Prog = PFib .carrier tt

ICar : ISort → Type₀
ICar prog = Prog
ICar res  = Res

-- THE `Fibered`.  Three operations, three kinds of splitting; the third
-- one IS the operational semantics.

ISplit : (o : ISAOp) → ICar (ISAResult o) → Type₀
ISplit seqop p  = PFib .Split appop p
ISplit sepop h  = Fib  .Split appop h
ISplit runop h' = Σ[ p ∈ Prog ] Σ[ h ∈ Res ] Run p h h'

IParts : (o : ISAOp) (m : ICar (ISAResult o))
       → ISplit o m → (a : ISAAr o) → ICar (ISASortOf o a)
IParts seqop p  sp          = PFib .parts appop p sp
IParts sepop h  sp          = Fib  .parts appop h sp
IParts runop h' (p , h , _) = boolΠ {M = λ a → ICar (ISASortOf runop a)} p h

isaFib : Fibered isaSig ℓ-zero ℓ-zero
isaFib .carrier = ICar
isaFib .Split   = ISplit
isaFib .parts   = IParts

-- every connective, every additive rule, and `⊗ˢ`'s intro/elim
open RulesF isaFib public

-- assertions and program specifications, named
Asrt : (ℓ : Level) → Type (ℓ-suc ℓ)
Asrt ℓ = TheoryTy ℓ res

Spec : (ℓ : Level) → Type (ℓ-suc ℓ)
Spec ℓ = TheoryTy ℓ prog

-- THE TWO MONOIDAL CONNECTIVES.  Both are `⊗ˢ`; only the operation
-- differs, and with it the sort.

_∗_ : Asrt ℓA → Asrt ℓA → Asrt _
A ∗ B = ⊗ˢ sepop (boolΠ {M = λ _ → Asrt _} A B)

infixr 20 _∗_

-- (there is no `emp` here: the unit of `∗` is `⊗ˢ` at a NULLARY
-- operation, and `isaSig`'s three operations are all binary.  See the
-- closing note.)

_⍮_ : Spec ℓA → Spec ℓA → Spec _
P ⍮ Q = ⊗ˢ seqop (boolΠ {M = λ _ → Spec _} P Q)

infixr 20 _⍮_

-- STRONGEST POSTCONDITION = `⊗ˢ runop`.

spost : Spec ℓA → Asrt ℓA → Asrt _
spost P A = ⊗ˢ runop (boolΠ {M = λ a → TheoryTy _ (ISASortOf runop a)} P A)

-- WEAKEST PRECONDITION = the RESIDUAL of `runop` at the resource slot.

runFocus : Focus isaFib runop rslot
runFocus .SplitAt h            = Σ[ p ∈ Prog ] Σ[ h' ∈ Res ] Run p h h'
runFocus .whole (p , h' , _)   = h'
runFocus .Rest                 = Unit
runFocus .restOf _             = pslot
runFocus .restSlot (p , _ , _) = λ _ → p

open FocusNotation runFocus public

wpre : Spec ℓA → Asrt ℓB → Asrt _
wpre {ℓA = ℓA} P B =
  ⊸ᶠ (boolΠ {M = λ a → TheoryTy ℓA (ISASortOf runop a)} P ⊤G') B
  where
  ⊤G' : Asrt ℓA
  ⊤G' _ = Unit*

-- ... and the Hoare triple is an entailment at the sort `res`.
⟪_⟫_⟪_⟫ : Asrt ℓA → Spec ℓB → Asrt ℓC → Type _
⟪ A ⟫ P ⟪ B ⟫ = A ⊢ wpre P B

-- `sp ⊣ wp`, BY HAND ONCE. Both hom-sets curry to the same six-argument
-- function.

module _ (P : Spec ℓA) (A : Asrt ℓA) (B : Asrt ℓB) where

  spost⇒wpre : (spost P A ⊢ B) → ⟪ A ⟫ P ⟪ B ⟫
  spost⇒wpre f h a (p , h' , r) k =
    f h' ((p , h , r) , boolΠ {M = λ b → boolΠ {M = λ a' → TheoryTy _ (ISASortOf runop a')} P A b
                                                (IParts runop h' (p , h , r) b)}
                              (k tt) a)

  wpre⇒spost : ⟪ A ⟫ P ⟪ B ⟫ → (spost P A ⊢ B)
  wpre⇒spost g h' ((p , h , r) , pay) =
    g h (pay rslot) (p , h' , r) (λ _ → pay pslot)

  -- one direction is definitional ...
  sp⊣wp-β : (g : ⟪ A ⟫ P ⟪ B ⟫) → spost⇒wpre (wpre⇒spost g) ≡ g
  sp⊣wp-β g = refl

  -- ... and the other is `boolΠ`-η, pointwise
  sp⊣wp-η : (f : spost P A ⊢ B) → wpre⇒spost (spost⇒wpre f) ≡ f
  sp⊣wp-η f i h' (sp , pay) =
    f h' (sp , boolΠ-η (λ b → boolΠ {M = λ a' → TheoryTy _ (ISASortOf runop a')} P A b
                                     (IParts runop h' sp b))
                       pay i)
    where
    boolΠ-η : ∀ {ℓ} (M : Bool → Type ℓ) (k : (b : Bool) → M b)
            → boolΠ {M = M} (k true) (k false) ≡ k
    boolΠ-η M k = funExt λ { true → refl ; false → refl }

  sp⊣wp : Iso (spost P A ⊢ B) ⟪ A ⟫ P ⟪ B ⟫
  sp⊣wp .Iso.fun = spost⇒wpre
  sp⊣wp .Iso.inv = wpre⇒spost
  sp⊣wp .Iso.sec = sp⊣wp-β
  sp⊣wp .Iso.ret = sp⊣wp-η

-- THE RULE OF CONSEQUENCE.  Functoriality of `⊸ᶠ`, and therefore free:
-- no hypothesis on `Run` is used.

wpre-map : (P : Spec ℓA) {B B' : Asrt ℓB} → B ⊢ B' → wpre P B ⊢ wpre P B'
wpre-map P f h w sa k = f _ (w sa k)

wpre-spec : {P P' : Spec ℓA} (B : Asrt ℓB) → P' ⊢ P → wpre P B ⊢ wpre P' B
wpre-spec B s h w sa k = w sa (λ r → s _ (k r))

consequence : {A A' : Asrt ℓA} {B B' : Asrt ℓB} (P : Spec ℓC)
            → A' ⊢ A → B ⊢ B' → ⟪ A ⟫ P ⟪ B ⟫ → ⟪ A' ⟫ P ⟪ B' ⟫
consequence P pre post t = wpre-map P post ∘g t ∘g pre

-- THE ASSERTION-LEVEL FRAME RULE.  `⊗ˢ-map`, i.e. functoriality of the
-- spatial tensor.  Free, exactly as in `ISA.Machine`.

∗-map : {A B : Asrt ℓA} (C : Asrt ℓA) → A ⊢ B → (A ∗ C) ⊢ (B ∗ C)
∗-map {A = A} {B = B} C f =
  ⊗ˢ-map sepop {A = boolΠ {M = λ _ → Asrt _} A C} {B = boolΠ {M = λ _ → Asrt _} B C}
         (boolΠ {M = λ a → boolΠ {M = λ _ → Asrt _} A C a
                         ⊢ boolΠ {M = λ _ → Asrt _} B C a} f idg)

-- § THE TWO LAWS OF THE ACTION. These are `ISA.Interp.Interp`'s two
-- fields, restated.

-- `Run` is a LAX ACTION: running a program that splits is running the
-- two halves in turn.
LaxAction : Type₀
LaxAction =
  (p : Prog) (sp : PFib .Split appop p) (h h' : Res) → Run p h h'
  → Σ[ h₀ ∈ Res ] ( Run (PFib .parts appop p sp true)  h  h₀
                  × Run (PFib .parts appop p sp false) h₀ h' )

-- ... and the empty program does nothing.
UnitAction : Type₀
UnitAction =
  (p : Prog) → PFib .Split nilop p → (h h' : Res) → Run p h h' → h Eq.≡ h'

-- SEQUENCING, IN THE POSTCONDITION FORM. PRIMITIVE (phase 1): the one
-- place a `runop`-splitting is destructured.

module _ (act : LaxAction) where

  -- PRIMITIVE (phase 1). NOT for the reason the other hand-written clauses
  -- in this sweep had: `spost P A` IS `⊗ˢ runop (boolΠ P A)`, a connective
  -- composite already.
  spost-⍮ : (P Q : Spec ℓA) (A : Asrt ℓA)
          → spost (P ⍮ Q) A ⊢ spost Q (spost P A)
  spost-⍮ P Q A h' ((p , h , r) , pay) =
    ( PFib .parts appop p psp false , st .fst , st .snd .snd )
    , boolΠ {M = λ b → boolΠ {M = λ a' → TheoryTy _ (ISASortOf runop a')}
                              Q (spost P A) b
                              (IParts runop h'
                                ( PFib .parts appop p psp false
                                , st .fst , st .snd .snd ) b) }
            (pay pslot .snd false)
            ( ( PFib .parts appop p psp true , h , st .snd .fst )
            , boolΠ {M = λ b → boolΠ {M = λ a' → TheoryTy _ (ISASortOf runop a')}
                                      P A b
                                      (IParts runop (st .fst)
                                        ( PFib .parts appop p psp true
                                        , h , st .snd .fst ) b) }
                    (pay pslot .snd true)
                    (pay rslot) )
    where
    psp : PFib .Split appop p
    psp = pay pslot .fst

    st : Σ[ h₀ ∈ Res ] ( Run (PFib .parts appop p psp true)  h  h₀
                       × Run (PFib .parts appop p psp false) h₀ h' )
    st = act p psp h h' r

  -- ... AND THEREFORE THE HOARE SEQUENCING RULE, by transposition.
  -- No induction, no program, no case analysis: `sp⊣wp` twice and
  -- `spost-⍮` once.
  seqRule : {A M B : Asrt ℓA} (P Q : Spec ℓA)
          → ⟪ A ⟫ P ⟪ M ⟫ → ⟪ M ⟫ Q ⟪ B ⟫ → ⟪ A ⟫ P ⍮ Q ⟪ B ⟫
  seqRule {A = A} {M = M} {B = B} P Q t₁ t₂ =
    spost⇒wpre (P ⍮ Q) A B
      ( wpre⇒spost Q M B t₂
      ∘g ⊗ˢ-map runop
           {A = boolΠ {M = λ a → TheoryTy _ (ISASortOf runop a)} Q (spost P A)}
           {B = boolΠ {M = λ a → TheoryTy _ (ISASortOf runop a)} Q M}
           (boolΠ {M = λ a → boolΠ {M = λ a' → TheoryTy _ (ISASortOf runop a')} Q (spost P A) a
                           ⊢ boolΠ {M = λ a' → TheoryTy _ (ISASortOf runop a')} Q M a}
                  idg (wpre⇒spost P A M t₁))
      ∘g spost-⍮ P Q A )

-- THE EMPTY PROGRAM.

module _ (uni : UnitAction) where

  nilRule : (P : Spec ℓA) → ((p : Prog) → P p → PFib .Split nilop p)
          → (A : Asrt ℓB) → ⟪ A ⟫ P ⟪ A ⟫
  nilRule P isNil A h a (p , h' , r) k = coe (uni p (isNil p (k tt)) h h' r) a
    where
    coe : {x y : Res} → x Eq.≡ y → A x → A y
    coe Eq.refl z = z

-- § THE FRAME RULE. The one place the spatial and the temporal operation
-- interact, and it needs a hypothesis: LOCALITY.

Local : Prog → Type₀
Local p =
  (h : Res) (sep : Fib .Split appop h) (h' : Res) → Run p h h'
  → Σ[ sep' ∈ Fib .Split appop h' ]
      ( Run p (Fib .parts appop h sep true) (Fib .parts appop h' sep' true)
      × (Fib .parts appop h' sep' false Eq.≡ Fib .parts appop h sep false) )

module _ (P : Spec ℓA) (loc : (p : Prog) → P p → Local p) where

  frame-wpre : (B R : Asrt ℓA) → (wpre P B ∗ R) ⊢ wpre P (B ∗ R)
  frame-wpre B R =
    ⊗ˢ-E sepop {A = boolΠ {M = λ _ → Asrt _} (wpre P B) R}
      (λ h sep k (p , h' , r) j →
        let l    = loc p (j tt) h sep h' r
            sep' = l .fst
        in ⊗ˢ-I sepop {A = boolΠ {M = λ _ → Asrt _} B R} h' sep'
             (boolΠ {M = λ a → boolΠ {M = λ _ → Asrt _} B R a
                                 (Fib .parts appop h' sep' a)}
                    (k true ( p , Fib .parts appop h' sep' true , l .snd .fst) j)
                    (coeR (Eq.sym (l .snd .snd)) (k false))))
    where
    coeR : {x y : Res} → x Eq.≡ y → R x → R y
    coeR Eq.refl z = z

  frameRule : {A B : Asrt ℓA} (R : Asrt ℓA)
            → ⟪ A ⟫ P ⟪ B ⟫ → ⟪ A ∗ R ⟫ P ⟪ B ∗ R ⟫
  frameRule {A = A} {B = B} R t = frame-wpre B R ∘g ∗-map R t

-- § WHAT THE SIGNATURE DOES NOT HAVE. There is no `emp` and no `skip`
-- above.
