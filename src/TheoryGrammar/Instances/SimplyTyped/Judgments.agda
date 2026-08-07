{-
  THE BIDIRECTIONAL JUDGMENTS, as ONE `μ` with TWO nonterminals.

  The nonterminal index is `Mode × Ctx × Ty`, all at sort `tm`, so
  `Infer Γ A` and `Check Γ C` are two families of the same fixed point
  and the mode discipline is a property of the DESCRIPTION, not of a
  separate datatype:

    Infer  var    the name is bound in Γ, to the index type
           app    the function's type is A₀ ⇒ A for some GUESSED A₀,
                  whose argument is CHECKED
           ann    the term is checked at the type in the `ty` slot,
                  which the representable `⌈ A ⌉` pins to the index
    Check  switch synthesis at the very same type
           lam    only when the index type SPLITS as an arrow

  That last line is what the third sort buys: `⊕e (IsArr C)` IS the
  promodel's own `Split arrOp C`, so the rule is present exactly when
  the checking type is an arrow, with `dom`/`cod` read off by `parts`
  and no case analysis on `Ty` anywhere in the description.

  Two one-step unfoldings live here, side by side: `JStep`/`j-unroll`/
  `j-roll` at either nonterminal, and -- for the synthesis mode only --
  `SynStep`/`syn-out`/`syn-in`, which is `JStep` at `syn` with the
  `⊕ᴰ Ty` pushed past the coproduct.  The second is what a decision
  procedure needs, but it is a grammar isomorphism and decides nothing,
  so it is stated where its sibling is rather than in `Check.agda`.

  PRIMITIVE: `⟦J⟧`/`⟦J⟧⁻`, the container encoding respelled in the
  connectives (they never match a term and never open a splitting), and
  `varG-pull`, which reads a slot's index and republishes it at the
  whole.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Judgments where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt; tt*)
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Distributive
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Context

module Judgments (Name : Type₀) (_≟_ : Discrete Name) where

  open StBase Name
  open StContext Name _≟_

  -- `Mode` denotes the direction a judgment is read in: `syn` produces
  -- its type, `chk` consumes it.
  data Mode : Type₀ where
    syn chk : Mode

  -- `NT` denotes a nonterminal of the judgment grammar: a mode, the
  -- context it is under, and the type it produces or consumes.
  NT : Type₀
  NT = Mode × Ctx × Ty

  -- both nonterminals live at sort `tm`
  open Ind stlcFib ℓ-zero NT (λ _ → tm) public

  -- `InfTag`/`ChkTag` denote which RULE was used, one per alternative
  -- of the corresponding nonterminal.
  data InfTag : Type₀ where
    tVar tApp tAnn : InfTag

  data ChkTag : Type₀ where
    tSwitch tLam : ChkTag

  -- domain and codomain, read off a `ty`-splitting by `parts`.  Note
  -- there is no `Ty → Maybe Ty`: the CALLER holds an `IsArr` witness,
  -- so being an arrow is never re-established here.
  dom cod : {C : Ty} → IsArr C → Ty
  dom {C} sp = TParts arrOp C sp true
  cod {C} sp = TParts arrOp C sp false

  -- `JF x` denotes the one-step rule set at nonterminal `x`, as a
  -- container: a sum over rule tags of a tensor over that rule's slots.
  JF : (x : NT) → Functor tm
  JF (syn , Γ , A) = ⊕e InfTag λ
    { tVar → ⊗e varOp (λ _ → ⌜ Lookup Γ A ⌝)
    ; tApp → ⊕e Ty λ A₀ →
               ⊗e appOp (λ { true  → Var (syn , Γ , A₀ ⇒ᵗ A)
                           ; false → Var (chk , Γ , A₀) })
    ; tAnn → ⊗e annOp (λ { true  → Var (chk , Γ , A)
                         ; false → ⌜ ⌈_⌉ {s = ty} A ⌝ })
    }
  JF (chk , Γ , C) = ⊕e ChkTag λ
    { tSwitch → Var (syn , Γ , C)
    ; tLam → ⊕e (IsArr C) λ sa → ⊕e Name λ n →
               ⊗e lamOp (λ { true  → ⌜ Nm n ⌝
                           ; false → Var (chk , (n , dom sa) ∷ Γ , cod sa) })
    }

  -- `Jμ x` denotes the derivations at nonterminal `x`: the least fixed
  -- point of `JF`, indexed by the term derived.
  Jμ : NT → TmG
  Jμ x t = μ JF (x , t)

  -- `Infer Γ A` denotes "this term SYNTHESISES the type `A` in `Γ`";
  -- `Check Γ C` denotes "this term CHECKS against `C` in `Γ`".
  Infer Check : Ctx → Ty → TmG
  Infer Γ A = Jμ (syn , Γ , A)
  Check Γ C = Jμ (chk , Γ , C)

  -- `Syn Γ` denotes "this term synthesises SOME type in `Γ`", with the
  -- type carried as the sum's index.  Its subsingleton-ness -- one
  -- inhabited summand at most -- is the whole question (`Unique.agda`).
  Syn : Ctx → TmG
  Syn Γ = ⊕ᴰ Ty (Infer Γ)

  -- ================================================================
  -- One unfolding, in the connectives.
  -- ================================================================

  -- `JStep R x` denotes one layer of rules at `x`, with the recursive
  -- occurrences replaced by `R`: the same content as `⟦ JF x ⟧`, said
  -- in `⊕`/`⊕ᴰ`/`⊗ˢ` instead of shapes and positions.
  JStep : (NT → TmG) → NT → TmG
  JStep R (syn , Γ , A) =
      VarG (Lookup Γ A)
    ⊕ (⊕ᴰ Ty (λ A₀ → AppG (R (syn , Γ , A₀ ⇒ᵗ A)) (R (chk , Γ , A₀)))
    ⊕ AnnG (R (chk , Γ , A)) (⌈_⌉ {s = ty} A))
  JStep R (chk , Γ , C) =
      R (syn , Γ , C)
    ⊕ ⊕ᴰ (IsArr C) (λ sa → ⊕ᴰ Name (λ n →
        LamG (Nm n) (R (chk , (n , dom sa) ∷ Γ , cod sa))))

  -- PRIMITIVE: the two respellings.  `⟦J⟧` denotes "read a container
  -- layer as a layer of connectives" and `⟦J⟧⁻` the converse; together
  -- they say the shape/position presentation and the connective
  -- presentation of `JStep` are the same grammar.
  ⟦J⟧ : {M : Ix → Type₀} (x : NT) → ⟦ JF x ⟧ M ⊢ JStep (λ y t → M (y , t)) x
  ⟦J⟧ (syn , Γ , A) _ ((tVar , sp , sh) , _) = inl (sp , λ a → lower (sh a))
  ⟦J⟧ (syn , Γ , A) _ ((tApp , A₀ , sp , _) , rc) =
    inr (inl (A₀ , sp , λ { true → rc (true , tt*) ; false → rc (false , tt*) }))
  ⟦J⟧ (syn , Γ , A) _ ((tAnn , sp , sh) , rc) =
    inr (inr (sp , λ { true → rc (true , tt*) ; false → lower (sh false) }))
  ⟦J⟧ (chk , Γ , C) _ ((tSwitch , _) , rc) = inl (rc tt*)
  ⟦J⟧ (chk , Γ , C) _ ((tLam , sa , n , sp , sh) , rc) =
    inr (sa , n , sp , λ { true → lower (sh true) ; false → rc (false , tt*) })

  ⟦J⟧⁻ : {M : Ix → Type₀} (x : NT) → JStep (λ y t → M (y , t)) x ⊢ ⟦ JF x ⟧ M
  ⟦J⟧⁻ (syn , Γ , A) _ (inl (sp , h)) =
    (tVar , sp , λ a → lift (h a)) , λ { (_ , ()) }
  ⟦J⟧⁻ (syn , Γ , A) _ (inr (inl (A₀ , sp , h))) =
    (tApp , A₀ , sp , λ { true → tt* ; false → tt* })
      , λ { (true , _) → h true ; (false , _) → h false }
  ⟦J⟧⁻ (syn , Γ , A) _ (inr (inr (sp , h))) =
    (tAnn , sp , λ { true → tt* ; false → lift (h false) })
      , λ { (true , _) → h true ; (false , ()) }
  ⟦J⟧⁻ (chk , Γ , C) _ (inl d) = (tSwitch , tt*) , λ _ → d
  ⟦J⟧⁻ (chk , Γ , C) _ (inr (sa , n , sp , h)) =
    (tLam , sa , n , sp , λ { true → lift (h true) ; false → tt* })
      , λ { (true , ()) ; (false , _) → h false }

  -- from here down, nothing matches
  j-unroll : (x : NT) → Jμ x ⊢ JStep Jμ x
  j-unroll x = ⟦J⟧ x ∘g μ-coalg JF x

  j-roll : (x : NT) → JStep Jμ x ⊢ Jμ x
  j-roll x = μ-alg JF x ∘g ⟦J⟧⁻ x

  -- ================================================================
  -- The five rules: `roll` after a coproduct injection.
  -- ================================================================

  inf-var : (Γ : Ctx) (A : Ty) → VarG (Lookup Γ A) ⊢ Infer Γ A
  inf-var Γ A = j-roll (syn , Γ , A) ∘g ⊕-I₁

  inf-app : (Γ : Ctx) (A₀ A : Ty)
          → AppG (Infer Γ (A₀ ⇒ᵗ A)) (Check Γ A₀) ⊢ Infer Γ A
  inf-app Γ A₀ A =
    j-roll (syn , Γ , A)
    ∘g (⊕-I₂ ∘g (⊕-I₁ ∘g ⊕ᴰ-I Ty
          {A = λ A₁ → AppG (Infer Γ (A₁ ⇒ᵗ A)) (Check Γ A₁)} A₀))

  inf-ann : (Γ : Ctx) (A : Ty)
          → AnnG (Check Γ A) (⌈_⌉ {s = ty} A) ⊢ Infer Γ A
  inf-ann Γ A = j-roll (syn , Γ , A) ∘g (⊕-I₂ ∘g ⊕-I₂)

  chk-switch : (Γ : Ctx) (C : Ty) → Infer Γ C ⊢ Check Γ C
  chk-switch Γ C = j-roll (chk , Γ , C) ∘g ⊕-I₁

  chk-lam : (Γ : Ctx) (C : Ty) (sa : IsArr C) (n : Name)
          → LamG (Nm n) (Check ((n , dom sa) ∷ Γ) (cod sa)) ⊢ Check Γ C
  chk-lam Γ C sa n =
    j-roll (chk , Γ , C)
    ∘g (⊕-I₂ ∘g (⊕ᴰ-I (IsArr C)
          {A = λ sa' → ⊕ᴰ Name (λ n' →
                 LamG (Nm n') (Check ((n' , dom sa') ∷ Γ) (cod sa')))} sa
        ∘g ⊕ᴰ-I Name
          {A = λ n' → LamG (Nm n') (Check ((n' , dom sa) ∷ Γ) (cod sa))} n))

  -- ================================================================
  -- THE SAME UNFOLDING FOR `Syn Γ`, with the ⊕ᴰ pushed inwards.
  --
  -- `JStep` says what ONE type's derivations look like; `SynStep` says
  -- what SOME type's do, which is the shape a decision procedure can
  -- recurse on -- at `var` the guessed type collapses into `Look Γ`,
  -- and at `app` two nested guesses become one over `Ty × Ty`.  All of
  -- it is grammar isomorphism; nothing here decides anything.
  -- ================================================================

  -- the three alternatives of `syn`, at a fixed synthesised type
  QVar : Ctx → Ty → TmG
  QVar Γ A = VarG (Lookup Γ A)

  QApp' : Ctx → Ty → TmG
  QApp' Γ A = ⊕ᴰ Ty (λ A₀ → AppG (Infer Γ (A₀ ⇒ᵗ A)) (Check Γ A₀))

  QAnn : Ctx → Ty → TmG
  QAnn Γ A = AnnG (Check Γ A) (⌈_⌉ {s = ty} A)

  -- `QApp Γ (A₀ , A)` denotes the application rule with BOTH types
  -- named at once, so that one `⊕ᴰ` guesses the pair
  QApp : Ctx → Ty × Ty → TmG
  QApp Γ AB = AppG (Infer Γ (AB .fst ⇒ᵗ AB .snd)) (Check Γ (AB .fst))

  SynApp : Ctx → TmG
  SynApp Γ = ⊕ᴰ (Ty × Ty) (QApp Γ)

  SynAnn : Ctx → TmG
  SynAnn Γ = ⊕ᴰ Ty (QAnn Γ)

  -- `SynStep Γ` denotes one layer of `Syn Γ`: a variable bound
  -- somewhere in `Γ`, an application, or an annotation.
  SynStep : Ctx → TmG
  SynStep Γ = VarG (Look Γ) ⊕ (SynApp Γ ⊕ SynAnn Γ)

  -- internal: the ⊕ᴰ goes INTO the unary tensor by its functorial action
  varG-push : (Γ : Ctx) → ⊕ᴰ Ty (QVar Γ) ⊢ VarG (Look Γ)
  varG-push Γ = ⊕ᴰ-E λ A →
    ⊗ˢ-map varOp {A = varFam (Lookup Γ A)} {B = varFam (Look Γ)}
           (λ _ → ⊕ᴰ-I Ty {A = Lookup Γ} A)

  -- PRIMITIVE: and out again.  This direction is NOT internal -- it
  -- reads the index out of a slot and republishes it at the whole --
  -- but for a UNARY operation it is only `Unit`'s η.
  varG-pull : (Γ : Ctx) → VarG (Look Γ) ⊢ ⊕ᴰ Ty (QVar Γ)
  varG-pull Γ t (sp , h) = h tt .fst , sp , λ _ → h tt .snd

  -- internal: reindexing an iterated ⊕ᴰ along a product
  appReindex : (Γ : Ctx) → ⊕ᴰ Ty (QApp' Γ) ⊢ SynApp Γ
  appReindex Γ = ⊕ᴰ-E λ A → ⊕ᴰ-E λ A₀ → ⊕ᴰ-I (Ty × Ty) {A = QApp Γ} (A₀ , A)

  appReindex⁻ : (Γ : Ctx) → SynApp Γ ⊢ ⊕ᴰ Ty (QApp' Γ)
  appReindex⁻ Γ = ⊕ᴰ-E λ AB →
      ⊕ᴰ-I Ty {A = QApp' Γ} (AB .snd)
    ∘g ⊕ᴰ-I Ty {A = λ A₀ → AppG (Infer Γ (A₀ ⇒ᵗ AB .snd)) (Check Γ A₀)} (AB .fst)

  syn-out : (Γ : Ctx) → Syn Γ ⊢ SynStep Γ
  syn-out Γ =
      ⊕-E (⊕-I₁ ∘g varG-push Γ)
          (⊕-I₂ ∘g (⊕-E (⊕-I₁ ∘g appReindex Γ) ⊕-I₂ ∘g ⊕ᴰ-⊕-out Ty))
    ∘g (⊕ᴰ-⊕-out Ty ∘g ⊕ᴰ-map Ty (λ A → j-unroll (syn , Γ , A)))

  syn-in : (Γ : Ctx) → SynStep Γ ⊢ Syn Γ
  syn-in Γ =
      ⊕ᴰ-map Ty (λ A → j-roll (syn , Γ , A))
    ∘g (⊕ᴰ-⊕-in Ty
        ∘g ⊕-E (⊕-I₁ ∘g varG-pull Γ)
               (⊕-I₂ ∘g (⊕ᴰ-⊕-in Ty
                         ∘g ⊕-E (⊕-I₁ ∘g appReindex⁻ Γ) ⊕-I₂)))
