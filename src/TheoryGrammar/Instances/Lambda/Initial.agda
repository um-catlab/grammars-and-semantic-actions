{- THE CARRIER IS THE INITIAL ALGEBRA: `⊤G ≅ Everything Γ = μ AllF`. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Induction
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.SemanticAction

module Initial (Name : Type₀) where

  open LamBase Name public

  Scope : Type₀
  Scope = List Name

  -- nonterminals: one per scope, all at sort `tm`.  `Induct` is `Ind`
  -- plus the DEPENDENT eliminator `indμ`, which `readback-unique` needs
  -- and which is stated once, generically, in `TheoryGrammar.Induction`.
  open Induct λFib ℓ-zero Scope (λ _ → tm) public

  private variable ℓM : Level

  -- The shape functor of λSig.

  data AllTag : Type₀ where
    aVar aApp aLam : AllTag

  -- the two slots of `lamOp` have DIFFERENT sorts, so this is the one
  -- slot family that is a genuine match; it is why `Sh` at `lamOp` has
  -- no η (see `readback-unique`)
  Glam : Scope → (a : LAr lamOp) → Functor (LSortOf lamOp a)
  Glam Γ true  = ⌜ ⊤G ⌝
  Glam Γ false = Var Γ

  AllF : Scope → Functor tm
  AllF Γ = ⊕e AllTag λ
    { aVar → ⊗e varOp (λ _ → ⌜ ⊤G ⌝)
    ; aApp → ⊗e appOp (λ _ → Var Γ)
    ; aLam → ⊗e lamOp (Glam Γ)
    }

  Everything : Scope → TmG
  Everything Γ t = μ AllF (Γ , t)

  -- The same functor in the CONNECTIVES.  `Lambda.Base`'s `VarG`/
  -- `AppG`/`LamG` are fixed at ℓ-zero and `indRaw`'s motive is not, so
  -- these are the same three tensors taken level-polymorphically.

  ⊤* : {s : LSort} → TheoryTy ℓM s
  ⊤* _ = Unit*

  VarA : (ℓM : Level) → TheoryTy ℓM tm
  VarA ℓM = ⊗ˢ varOp (λ _ → ⊤* {ℓM})

  AppA : TheoryTy ℓM tm → TheoryTy ℓM tm
  AppA M = ⊗ˢ appOp (λ _ → M)

  -- NAMED, not an extended lambda: `lamOp`'s slot family is the one that
  -- is a match on the arity, and two syntactically distinct pattern
  -- lambdas over `LAr lamOp` are never convertible (the same fact
  -- `readback-unique` pays `lamJ` for).
  LamSlots : TheoryTy ℓM tm → (a : LAr lamOp) → TheoryTy ℓM (LSortOf lamOp a)
  LamSlots M true  = ⊤*
  LamSlots M false = M

  LamA : TheoryTy ℓM tm → TheoryTy ℓM tm
  LamA M = ⊗ˢ lamOp (LamSlots M)

  AllStep : (Scope → TheoryTy ℓM tm) → Scope → TheoryTy ℓM tm
  AllStep {ℓM} M Γ = VarA ℓM ⊕ (AppA (M Γ) ⊕ LamA (M Γ))

  -- ... AND THEIR ELIMINATORS, at an arbitrary motive.

  -- `along-unsplit P o m sp` DENOTES: "a `P` of the reassembled parts is a
  -- `P` of the thing they came from".
  along-unsplit : (P : TheoryTy ℓM tm) (o : LOp) (m : Raw) (sp : LSplit o m)
                → P (Op o (LParts o m sp)) → P m
  along-unsplit P o m sp = Eq.transport P (λ-unsplit o m sp)

  VarA-E : {P : TheoryTy ℓM tm} → ((n : Name) → P (var n)) → VarA ℓM ⊢ P
  VarA-E {P = P} pv = ⊗ˢ-E varOp λ m sp _ →
    along-unsplit P varOp m sp (pv (LParts varOp m sp tt))

  AppA-E : {P : TheoryTy ℓM tm}
         → ((u v : Raw) → P u → P v → P (app u v)) → AppA P ⊢ P
  AppA-E {P = P} pa = ⊗ˢ-E appOp {A = λ _ → P} {B = P} λ m sp h →
    along-unsplit P appOp m sp
      (pa (LParts appOp m sp true) (LParts appOp m sp false) (h true) (h false))

  LamA-E : {P : TheoryTy ℓM tm}
         → ((n : Name) (t : Raw) → P t → P (lam n t)) → LamA P ⊢ P
  LamA-E {P = P} pl = ⊗ˢ-E lamOp {A = LamSlots P} {B = P}
    λ m sp h → along-unsplit P lamOp m sp
      (pl (LParts lamOp m sp true) (LParts lamOp m sp false) (h false))

  -- PRIMITIVE (1 of 2): the container encoding respelled in the
  -- connectives, exactly as `Scoped.⟦Sc⟧`.  Nothing is matched but the
  -- tag and the boolean slot; `sp` passes through abstractly.
  ⟦All⟧ : {M : Ix → Type ℓM} (Γ : Scope)
        → ⟦ AllF Γ ⟧ M ⊢ AllStep (λ Δ x → M (Δ , x)) Γ
  ⟦All⟧ Γ _ ((aVar , sp , _) , _)  = inl (sp , λ _ → tt*)
  ⟦All⟧ Γ _ ((aApp , sp , _) , rc) =
    inr (inl (sp , λ { true → rc (true , tt*) ; false → rc (false , tt*) }))
  ⟦All⟧ Γ _ ((aLam , sp , _) , rc) =
    inr (inr (sp , λ { true → tt* ; false → rc (false , tt*) }))

  ⟦All⟧⁻ : {M : Ix → Type ℓM} (Γ : Scope)
         → AllStep (λ Δ x → M (Δ , x)) Γ ⊢ ⟦ AllF Γ ⟧ M
  ⟦All⟧⁻ Γ _ (inl (sp , _)) = (aVar , sp , λ _ → lift tt) , λ { (_ , ()) }
  ⟦All⟧⁻ Γ _ (inr (inl (sp , h))) =
    (aApp , sp , λ _ → tt*) , λ { (true , _) → h true ; (false , _) → h false }
  ⟦All⟧⁻ Γ _ (inr (inr (sp , h))) =
    (aLam , sp , λ { true → lift tt ; false → tt* })
      , λ { (true , ()) ; (false , _) → h false }

  -- from here down, nothing matches
  all-unroll : (Γ : Scope) → Everything Γ ⊢ AllStep Everything Γ
  all-unroll Γ = ⟦All⟧ Γ ∘g μ-coalg AllF Γ

  all-roll : (Γ : Scope) → AllStep Everything Γ ⊢ Everything Γ
  all-roll Γ = μ-alg AllF Γ ∘g ⟦All⟧⁻ Γ

  all-var : (Γ : Scope) → VarA ℓ-zero ⊢ Everything Γ
  all-var Γ = all-roll Γ ∘g ⊕-I₁

  all-app : (Γ : Scope) → AppA (Everything Γ) ⊢ Everything Γ
  all-app Γ = all-roll Γ ∘g (⊕-I₂ ∘g ⊕-I₁)

  all-lam : (Γ : Scope) → LamA (Everything Γ) ⊢ Everything Γ
  all-lam Γ = all-roll Γ ∘g (⊕-I₂ ∘g ⊕-I₂)

  -- INITIALITY.

  -- PRIMITIVE (2 of 2): every element of the carrier is uniquely built
  -- from the operations.  The only recursion on `Raw` in the tree.
  readback : (Γ : Scope) → ⊤G ⊢ Everything Γ
  readback Γ (var n) _ =
    all-var Γ (var n) (mkVar n , λ _ → tt*)
  readback Γ (app u v) _ =
    all-app Γ (app u v)
      (mkApp u v , λ { true → readback Γ u tt ; false → readback Γ v tt })
  readback Γ (lam n t) _ =
    all-lam Γ (lam n t)
      (mkLam n t , λ { true → tt* ; false → readback Γ t tt })

  forget : (Γ : Scope) → Everything Γ ⊢ ⊤G
  forget Γ = ⊤-I

  -- one half of the isomorphism, free: ⊤G is terminal
  forget-readback : (Γ : Scope) (t : Raw) (u : ⊤G t)
                  → forget Γ t (readback Γ t u) ≡ u
  forget-readback Γ t u = refl

  -- The other half: nothing else inhabits `μ AllF`.  That is a
  -- statement ABOUT an element, so it is proved by `indμ` -- the
  -- dependent eliminator, taken from `TheoryGrammar.Induction`.

  -- PRIVATE, and deliberately so: unlike `along-unsplit`, none of these is
  -- a lemma anyone could reuse.
  private
    supf : {Γ : Scope} {m : Raw} (sh : Sh (AllF Γ) m)
         → ((p : Pos (AllF Γ) m sh) → μ AllF (nx (AllF Γ) m sh p))
         → μ AllF (Γ , m)
    supf sh f = sup sh f

    -- MEASUREMENT. `varOp`/`appOp` are `refl`: their slot families are
    -- constant, so the shape has η.
    ShLam : (Γ : Scope) (n : Name) (t : Raw) → Type₀
    ShLam Γ n t = (a : LAr lamOp)
                → Sh (Glam Γ a) (LParts lamOp (lam n t) (mkLam n t) a)

    -- the canonical lam shape, taken FROM `readback` rather than
    -- rewritten: two syntactically distinct pattern lambdas over an
    -- arity are never convertible, so it has to be this one
    shLam0 : (Γ : Scope) (n : Name) (t : Raw) → ShLam Γ n t
    shLam0 Γ n t = unroll (readback Γ (lam n t) tt) .fst .snd .snd

    LamMot : (Γ : Scope) (n : Name) (t : Raw) → ShLam Γ n t → Type₀
    LamMot Γ n t sh =
        (f : (p : Pos (AllF Γ) (lam n t) (aLam , mkLam n t , sh))
           → μ AllF (nx (AllF Γ) (lam n t) (aLam , mkLam n t , sh) p))
      → ((p : Pos (AllF Γ) (lam n t) (aLam , mkLam n t , sh))
         → readback (nx (AllF Γ) (lam n t) (aLam , mkLam n t , sh) p .fst)
                    (nx (AllF Γ) (lam n t) (aLam , mkLam n t , sh) p .snd) tt
           ≡ f p)
      → readback Γ (lam n t) tt ≡ supf (aLam , mkLam n t , sh) f

    lamJ : (Γ : Scope) (n : Name) (t : Raw) (sh : ShLam Γ n t)
         → shLam0 Γ n t ≡ sh → LamMot Γ n t sh
    lamJ Γ n t sh =
      J (λ sh' _ → LamMot Γ n t sh')
        (λ f ih → cong (supf (aLam , mkLam n t , shLam0 Γ n t))
                       (funExt λ { (true , ()) ; (false , q) → ih (false , q) }))

  readback-unique : (Γ : Scope) (t : Raw) (e : Everything Γ t)
                  → readback Γ t tt ≡ e
  readback-unique Γ t = indμ (λ i e → readback (i .fst) (i .snd) tt ≡ e) α (Γ , t)
    where
    α : (Δ : Scope) (m : Raw) (sh : Sh (AllF Δ) m)
        (f : (p : Pos (AllF Δ) m sh) → μ AllF (nx (AllF Δ) m sh p))
      → ((p : Pos (AllF Δ) m sh)
         → readback (nx (AllF Δ) m sh p .fst) (nx (AllF Δ) m sh p .snd) tt ≡ f p)
      → readback Δ m tt ≡ supf sh f
    α Δ _ (aVar , mkVar n , sh) f ih =
      cong (supf (aVar , mkVar n , sh)) (funExt λ { (_ , ()) })
    α Δ _ (aApp , mkApp u v , sh) f ih =
      cong (supf (aApp , mkApp u v , sh))
           (funExt λ { (true , q) → ih (true , q) ; (false , q) → ih (false , q) })
    α Δ _ (aLam , mkLam n t , sh) f ih =
      lamJ Δ n t sh (funExt λ { true → refl ; false → refl }) f ih

  -- ⊤G ≅ Everything Γ: the carrier IS the initial algebra of `AllF`.
  ⊤≅Everything : (Γ : Scope) (t : Raw) → Iso (⊤G t) (Everything Γ t)
  ⊤≅Everything Γ t .Iso.fun = readback Γ t
  ⊤≅Everything Γ t .Iso.inv = forget Γ t
  ⊤≅Everything Γ t .Iso.sec = readback-unique Γ t
  ⊤≅Everything Γ t .Iso.ret = forget-readback Γ t

  -- The algebra `fold` is applied to: unique readability at an
  -- ARBITRARY motive level.

  -- DERIVED: `⟦All⟧` respells the container as `VarA ⊕ (AppA ⊕ LamA)`, and
  -- the three tensors are then eliminated by the rules above.
  AllAlg : (P : Raw → Type ℓM)
         → ((n : Name) → P (var n))
         → ((u v : Raw) → P u → P v → P (app u v))
         → ((n : Name) (t : Raw) → P t → P (lam n t))
         → (Γ : Scope) (m : Raw) (sh : Sh (AllF Γ) m)
         → ((p : Pos (AllF Γ) m sh) → P (nx (AllF Γ) m sh p .snd)) → P m
  AllAlg P pv pa pl Γ m sh rc =
    ⊕-E (VarA-E pv) (⊕-E (AppA-E pa) (LamA-E pl))
        m (⟦All⟧ {M = λ i → P (i .snd)} Γ m (sh , rc))

  -- `readback` is a MAP OUT OF `⊤` at the shape `Result ⊥G` -- it cannot
  -- fail.

  module AI = ActInd λFib ℓ-zero Scope (λ _ → tm)

  SzMot : Ix → Type₀
  SzMot i = Δ ℕ (i .snd)

  szAlg : AI.ActAlg AllF (λ _ → ℕ)
  szAlg Γ = ⊕ᴰ-E λ
    { aVar → pureA ℕ 1
    ; aApp → mapA (λ f → suc (f true + f false))
                  (⊗A appOp {A = λ _ → ⟦ Var Γ ⟧c SzMot} (λ _ → ℕ)
                      (λ { true → idA ; false → idA }))
    ; aLam → mapA (λ f → suc (f false))
                  (⊗A lamOp {A = λ a → ⟦ Glam Γ a ⟧c SzMot}
                      (λ { true → Unit ; false → ℕ })
                      (λ { true → pureA Unit tt ; false → idA }))
    }

  -- ... and the observation is a TERM: `⊤G ⊢ Δ ℕ`, not `Raw → ℕ`.
  -- `run` belongs at the test, not here.
  size! : (Γ : Scope) → ⊤G ⊢ Δ ℕ
  size! Γ = AI.recA szAlg Γ ∘g readback Γ
