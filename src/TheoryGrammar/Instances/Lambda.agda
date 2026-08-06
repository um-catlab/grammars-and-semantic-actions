{-
  A GENUINELY TWO-SORTED INSTANCE: lambda ASTs over sorts `nm` and `tm`.

  This is the port of `Grammar/LambdaScope.agda` onto the current
  `TheoryGrammar` stack, and it is a port with a change of design: the
  old version was SINGLE-sorted and paid for it by indexing the
  OPERATIONS by names --

      varOp n  (arity ⊥)     appOp  (arity Bool)     lamOp n  (arity Unit)

  -- i.e. one operation per name, so `ops` was as big as `Name`, `Split`
  had to be a family of predicates `IsVar n`/`IsLam n`, and names were
  not objects of the calculus at all.

  With two sorts the signature has exactly THREE operations and names
  become a sort:

      sorts        nm , tm
      varOp        arity Unit,  slot at nm            -> tm
      appOp        arity Bool,  both slots at tm      -> tm
      lamOp        arity Bool,  slot true  at nm      -> tm
                                slot false at tm

  `lamOp` is the point of the exercise: its two slots have DIFFERENT
  sorts, so `sortOf lamOp` is a non-constant function and the sort
  machinery is actually exercised (the monoid/string instance has
  `S = Unit`, so it never is).

  What two-sortedness buys, concretely:

    * `TheoryTy ℓ nm = Name → Type` is a grammar sort in its own right,
      so a SCOPE is a grammar: `In Γ : NmG`.  The old version had to
      smuggle `n ∈ Γ` in as a side condition on the operation label.
    * `⌈ n ⌉` at sort `nm` is the representable that pins a binder.  The
      old `lamOp n` is recovered as `⊗[lamOp] (⌈ n ⌉ , -)`, so the
      family of operations collapses into one operation applied to a
      family of grammars.
    * residuals exist AT SORT `nm`: `⊸ᶠ` at (lamOp, true) is a grammar
      over names -- "what a name has to satisfy for `λ-. body` to be a
      whole".  There is no single-sorted analogue.
    * `varOp` has arity `Unit`, and `Unit` has definitional η, so its
      adjunction has strictly better computational behaviour than the
      `Bool`-encoded binary ones.  Measured in §4.

  Every `Split o t` here has exactly ONE constructor, which is unique
  readability of the AST; that is what makes these grammars unambiguous
  for free, and it is a property of the SUBSTRATE, not of any grammar
  written over it.

  Sections:
    1  the signature                    6  toDB, as the generic fold
    2  the substrate                    7  grading: every splitting proper
    3  the connectives                  8  decidability -- all inherited
    4  residuals, and the measurements  9  the binder: Yoneda
    5  Scoped, as the generic μ        10  the scope checker
                                       11  it computes

  WORKING INTERNALLY.  The algorithms in §6 and §10 are compositions of
  combinators.  In particular DECIDABILITY IS A CONNECTIVE, not a
  metalanguage type: a decision for `A` is a map `⊤ ⊢ A ⊕ A'` together
  with `(A & A') ⊢ ⊥`, and `Dec⟨ A ⟩` is the default complement
  `A' = ¬G A = A ⇒ ⊥`.  None of that theory lives here -- it is generic
  in the theory and lives in `TheoryGrammar.Decidable`, which this file
  merely instantiates.  There is no `Dec`, no `⊎`, no `Maybe`, no
  `yes`/`no` in any statement, and the tests observe a decision with
  `⊕-E` into a constant grammar rather than by matching it.

  That discipline is only meaningful if the set of things that ARE
  allowed to match is small and named, so here it is in full -- every
  other definition in this file is a composite of these:

    §2  the substrate itself: `Op`, `LSplit`, `LParts`, `split`.
        These ARE the representation; there is nothing to derive them
        from.
    §3  `var-mk`/`app-mk`/`lam-mk` and `var-elim`/`app-elim`/`lam-elim`
        -- intro and elim of the three tensors.
    §5  `⟦Sc⟧`/`⟦Sc⟧⁻`, the container encoding of `ScopedF` respelled in
        the connectives.  One per description; `sc-roll`, `sc-unroll`,
        the three rules, the elaborator and the checker all factor
        through it.  It never opens a splitting -- `sp` passes through
        abstractly -- so it is a change of notation, not a proof.
    §7  `size`, the grading, and `proper`, which says every slot of every
        splitting is strictly smaller.
    §8  the `DecReadable` record: `Split-isProp` (at most one splitting),
        `⊗-decSplit` (and it is decidable whether there is one), and
        `λ-decSlots` (slotwise decisions combine -- the one place the
        FINITENESS of the arity is used).
    §9  `collapse`/`collapse⁻`, Yoneda for the binder, and `dec-lamᵈ`.

  The scope checker is then: unfold one step, decide each of the three
  summands with the generic `dec-⊗`, recombine with the generic `dec-⊕`,
  fold back.  The recursive calls sit at `LParts o t sp a` and `proper`
  is exactly the descent proof they need, which is what "the checker is
  a hylo with no side condition" means here -- the side condition was
  discharged once, for the substrate.

  THE REMAINING EXTERNALITY, named honestly.  `λ-decSlots` and `dec-⊗`
  eliminate a sum sitting at a SLOT and land at the WHOLE.  The internal
  `⊕-E` preserves the index and so cannot do that; the connective that
  moves between a slot and the whole is the residual `⊸ᶠ` of §4.  Worse,
  the deciders for the recursive slots exist only at the PARTS, which is
  what `▷` in the sibling `TheoryGrammar.Graded` internalises.  Rebuilding
  `λ-decSlots` through `⊸ᶠ-UP` and `check` on `Guard.löb` is what would
  make this internal all the way down; the cost to watch is that
  `Guard.löb` goes through `WFI.induction`, whereas §7's fuel recursor is
  what makes §11's `refl` tests reduce.

  WHAT HOLDS BY `refl`, AND WHAT DOES NOT (the measurement asked for):

    parts-split at varOp        refl        (Unit has η)
    parts-split at appOp/lamOp  funExt      (Bool has none), refl inside
    ⊗-UP-β / ⊗-UP-η             refl        generic, Substrate.agda
    ⊸ᶠ-β / ⊸ᶠ-η at all four
      foci, INCLUDING the two
      cross-sorted ones         refl        generic, Substrate.agda
    var-β  (unary op)           refl
    var-η  (unary op)           funExt over `∀ t` only, refl inside
    fun-β  (binary op)          refl
    fun-η  (binary op)          funExt over `∀ t` AND over the arity

  So the arity of the operation, not the number of sorts, is what costs.
  Nothing in the sort machinery degrades any law: the residual at the
  binder slot -- whose source and target live at different sorts -- has
  exactly the same definitional β/η as the single-sorted ones.

  One inference cost worth recording, since it shapes how the whole DSL
  reads: a grammar-valued IMPLICIT argument is not inferable at a use
  site that lives under a term index.  The metavariable's context
  already contains the index `t`, so the constraint `?A t ≡ B t` is not
  a Miller pattern and stays blocked.  That is why `dec-yes`/`dec-no`,
  `dec-⊕`, `dec-map` and `dec-⊗` all take their grammars EXPLICITLY.  It
  is a consequence of grammars being POINTWISE (`carrier s → Type`)
  rather than abstract objects of a category, and it is the same reason
  `Strings.agda` reports endemic unsolved metas when `{A}`/`{B}` are
  left implicit.

  A second trap, one level down: `⌈⌉-E` matches `Eq.refl`, but a witness
  produced from `Discrete Name` via `pathToEq` does not reduce to
  `Eq.refl` in cubical.  `toIx` in §6 therefore discards the
  representable instead of eliminating it -- the de Bruijn index is
  determined by the POSITION in the scope, not by the proof -- and that
  is the difference between §11's tests computing and not.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order
  using (_<_; _≤_; ≤-refl; ≤-trans; suc-≤-suc; pred-≤-pred; zero-≤; ¬-<-zero; ≤SumLeft; ≤SumRight)
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary.Base using (Dec; yes; no; ¬_; Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesSub
open import TheoryGrammar.Decidable
open import TheoryGrammar.Inductive

-- ==================================================================
-- 1.  THE SIGNATURE.  Two sorts, three operations, mixed-sort arity.
-- ==================================================================

data LSort : Type₀ where
  nm tm : LSort

data LOp : Type₀ where
  varOp appOp lamOp : LOp

LAr : LOp → Type₀
LAr varOp = Unit
LAr appOp = Bool
LAr lamOp = Bool

-- THE non-constant `sortOf`: `lamOp` binds a NAME and a TERM.
LSortOf : (o : LOp) → LAr o → LSort
LSortOf varOp _     = nm
LSortOf appOp _     = tm
LSortOf lamOp true  = nm
LSortOf lamOp false = tm

λSig : SortedSig LSort ℓ-zero ℓ-zero
λSig .ops          = LOp
λSig .arities      = LAr
λSig .sortOf       = LSortOf
λSig .resultSort _ = tm

module Lam (Name : Type₀) (_≟_ : Discrete Name) where

  -- ================================================================
  -- 2.  THE SUBSTRATE.
  -- ================================================================

  data Raw : Type₀ where
    var : Name → Raw
    app : Raw → Raw → Raw
    lam : Name → Raw → Raw

  Carrier : LSort → Type₀
  Carrier nm = Name
  Carrier tm = Raw

  Op : (o : LOp) → ((a : LAr o) → Carrier (LSortOf o a)) → Raw
  Op varOp f = var (f tt)
  Op appOp f = app (f true) (f false)
  Op lamOp f = lam (f true) (f false)

  -- Splittings as data, indexed by the output.  ONE constructor each:
  -- that is unique readability, and it is why `parts` is a projection
  -- and not an inversion lemma.
  data IsVar : Raw → Type₀ where
    mkVar : (n : Name) → IsVar (var n)

  data IsApp : Raw → Type₀ where
    mkApp : (u v : Raw) → IsApp (app u v)

  data IsLam : Raw → Type₀ where
    mkLam : (n : Name) (t : Raw) → IsLam (lam n t)

  LSplit : (o : LOp) → Raw → Type₀
  LSplit varOp = IsVar
  LSplit appOp = IsApp
  LSplit lamOp = IsLam

  LParts : (o : LOp) (t : Raw) → LSplit o t → (a : LAr o) → Carrier (LSortOf o a)
  LParts varOp _ (mkVar n)   _     = n
  LParts appOp _ (mkApp u v) b     = if b then u else v
  LParts lamOp _ (mkLam n t) true  = n
  LParts lamOp _ (mkLam n t) false = t

  λSub : Substrate λSig ℓ-zero ℓ-zero
  λSub .carrier       = Carrier
  λSub .op            = Op
  λSub .Split         = LSplit
  λSub .parts         = LParts
  λSub .split varOp f = mkVar (f tt)
  λSub .split appOp f = mkApp (f true) (f false)
  λSub .split lamOp f = mkLam (f true) (f false)
  -- MEASUREMENT.  `varOp` is refl -- `Unit` has definitional η, so
  -- `λ a → f tt` already IS `f`.  The two `Bool`-arity operations need
  -- funExt, with refl at each slot: exactly the cost the string
  -- instance reports for `⟜-η`, and for exactly the same reason.
  λSub .parts-split varOp f = refl
  λSub .parts-split appOp f = funExt λ { true → refl ; false → refl }
  λSub .parts-split lamOp f = funExt λ { true → refl ; false → refl }

  -- The whole combinator layer, in one open: `SubNotation`'s
  -- connectives, `Rules`' intro/elim for every additive (via
  -- `RulesSub.RulesS`), and the generic internal decision theory of
  -- `TheoryGrammar.Decidable`.
  open DecSub λSub public

  -- ================================================================
  -- 3.  THE CONNECTIVES.  One per operation, as always -- but now they
  --     have mixed sorts in their arguments.
  -- ================================================================

  TmG : Type₁
  TmG = TheoryTy ℓ-zero tm          -- Raw  → Type

  NmG : Type₁
  NmG = TheoryTy ℓ-zero nm          -- Name → Type

  VarG : NmG → TmG
  VarG P = ⊗ˢ varOp (λ _ → P)

  AppG : TmG → TmG → TmG
  AppG A B = ⊗ˢ appOp (λ b → if b then A else B)

  -- The mixed-sort tensor.  `if_then_else_` cannot express this: the two
  -- branches live in DIFFERENT types (`NmG` and `TmG`).
  LamG : NmG → TmG → TmG
  LamG P A = ⊗ˢ lamOp (λ { true → P ; false → A })

  -- PRIMITIVES.  These are the only definitions in this file that look
  -- at a representation; everything below is built from them.
  var-mk : {P : NmG} {n : Name} → P n → VarG P (var n)
  var-mk {n = n} p = mkVar n , λ _ → p

  app-mk : {A B : TmG} {u v : Raw} → A u → B v → AppG A B (app u v)
  app-mk {u = u} {v} a b = mkApp u v , λ { true → a ; false → b }

  lam-mk : {P : NmG} {A : TmG} {n : Name} {t : Raw}
         → P n → A t → LamG P A (lam n t)
  lam-mk {n = n} {t} p a = mkLam n t , λ { true → p ; false → a }

  var-elim : {P : NmG} {C : TmG} → (∀ n → P n → C (var n)) → VarG P ⊢ C
  var-elim f _ (mkVar n , h) = f n (h tt)

  app-elim : {A B C : TmG} → (∀ u v → A u → B v → C (app u v)) → AppG A B ⊢ C
  app-elim f _ (mkApp u v , h) = f u v (h true) (h false)

  lam-elim : {P : NmG} {A : TmG} {C : TmG}
           → (∀ n t → P n → A t → C (lam n t)) → LamG P A ⊢ C
  lam-elim f _ (mkLam n t , h) = f n t (h true) (h false)

  -- ================================================================
  -- 4.  RESIDUALS, AND WHAT THEY COST.
  --
  --     `Focus λSub o i` is a one-hole context at slot `i` of `o`.  The
  --     residual it classifies is a grammar AT THE SORT OF THAT SLOT --
  --     so focusing `lamOp` at its binder gives a grammar over NAMES.
  -- ================================================================

  -- (a) the function position of an application: `C ⟜ A`.
  focFun : Focus λSub appOp true
  focFun .SplitAt _   = Raw            -- the argument
  focFun .whole {u} v = app u v
  focFun .Rest        = Unit
  focFun .restOf _    = false
  focFun .restSlot v _ = v

  module F = FocusNotation focFun

  _⟜ᵃ_ : TmG → TmG → TmG
  C ⟜ᵃ B = F.⊸ᶠ (λ b → if b then C else B) C

  -- (b) THE BINDER SLOT.  A residual at sort `nm`: a predicate on names.
  --     `⊸ᵇ A C` at `n` says "if the body satisfies A then `λ n. body`
  --     satisfies C".  Nothing single-sorted can state this.
  focBind : Focus λSub lamOp true
  focBind .SplitAt _   = Raw           -- the body
  focBind .whole {n} t = lam n t
  focBind .Rest        = Unit
  focBind .restOf _    = false
  focBind .restSlot t _ = t

  module B = FocusNotation focBind

  Binds : TmG → TmG → NmG
  Binds A C = B.⊸ᶠ (λ { true → ⊤G ; false → A }) C

  -- (c) the body slot of `lamOp`: a residual at sort `tm`, whose
  --     complement is the NAME.  Cross-sorted in the other direction.
  focBody : Focus λSub lamOp false
  focBody .SplitAt _   = Name
  focBody .whole {t} n = lam n t
  focBody .Rest        = Unit
  focBody .restOf _    = true
  focBody .restSlot n _ = n

  module Y = FocusNotation focBody

  Under : NmG → TmG → TmG
  Under P C = Y.⊸ᶠ (λ { true → P ; false → ⊤G }) C

  -- (d) `varOp`: arity `Unit`, so the complement of its only slot is
  --     EMPTY.  This is the best-behaved residual in the file.
  focVar : Focus λSub varOp tt
  focVar .SplitAt _   = Unit
  focVar .whole {n} _ = var n
  focVar .Rest        = ⊥
  focVar .restOf ()
  focVar .restSlot _ ()

  module V = FocusNotation focVar

  Wraps : TmG → NmG
  Wraps C = V.⊸ᶠ (λ _ → ⊤G) C

  -- The universal property of each residual is the generic one, and it
  -- is DEFINITIONAL -- including for the two cross-sorted foci, where
  -- the hom-set on the left is at one sort and the one on the right at
  -- the other.  Nothing about sorts interferes with β/η.
  bind-UP : {A C : TmG}
          → Iso (⊤G ⊢ Binds A C)
                (B.FocusedHom {A = λ { true → ⊤G ; false → A }} {B = C})
  bind-UP {A} {C} = B.⊸ᶠ-UP {A = λ { true → ⊤G ; false → A }} {B = C}

  body-UP : {P : NmG} {C : TmG}
          → Iso (⊤G ⊢ Under P C)
                (Y.FocusedHom {A = λ { true → P ; false → ⊤G }} {B = C})
  body-UP {P} {C} = Y.⊸ᶠ-UP {A = λ { true → P ; false → ⊤G }} {B = C}

  -- ----------------------------------------------------------------
  -- The β/η of each residual is `refl`, generically (Substrate.⊸ᶠ-β/η).
  -- What is NOT generic is the ADJUNCTION with the tensor.  Here is the
  -- measurement, for the two extreme arities.
  -- ----------------------------------------------------------------

  -- unary operation, `Unit` arity: BOTH directions definitional.
  module _ {P : NmG} {C : TmG} where

    var-curry : VarG P ⊢ C → P ⊢ Wraps C
    var-curry f n p _ _ = f (var n) (mkVar n , λ _ → p)

    var-uncurry : P ⊢ Wraps C → VarG P ⊢ C
    var-uncurry g = var-elim λ n p → g n p tt (λ ())

    -- β: refl.  `Unit` η collapses `λ _ → p` and the `SplitAt`, and the
    -- empty `Rest` is discharged by the absurd lambda -- no funExt.
    var-β : (g : P ⊢ Wraps C) → var-curry (var-uncurry g) ≡ g
    var-β g = refl

    -- η: one funExt to reach under `∀ t`, then the splitting is matched
    -- and everything inside is refl.  Contrast `⟜-η` for strings, where
    -- the funExt is needed OVER THE ARITY, inside a `cong`.
    var-η : (f : VarG P ⊢ C) → var-uncurry (var-curry f) ≡ f
    var-η f = funExt λ _ → funExt λ { (mkVar n , h) → refl }

    var-UP : Iso (VarG P ⊢ C) (P ⊢ Wraps C)
    var-UP .Iso.fun = var-curry
    var-UP .Iso.inv = var-uncurry
    var-UP .Iso.sec = var-β
    var-UP .Iso.ret = var-η

  -- binary operation, `Bool` arity: β still definitional, η needs a
  -- funExt over the arity.  Same shape as the string instance's ⟜UMP.
  module _ {A C : TmG} {B : TmG} where

    fun-curry : AppG A B ⊢ C → A ⊢ (C ⟜ᵃ B)
    fun-curry f u a v h = f (app u v) (mkApp u v , λ { true → a ; false → h tt })

    fun-uncurry : A ⊢ (C ⟜ᵃ B) → AppG A B ⊢ C
    fun-uncurry g = app-elim λ u v a b → g u a v (λ _ → b)

    fun-β : (g : A ⊢ (C ⟜ᵃ B)) → fun-curry (fun-uncurry g) ≡ g
    fun-β g = refl

    fun-η : (f : AppG A B ⊢ C) → fun-uncurry (fun-curry f) ≡ f
    fun-η f = funExt λ _ → funExt λ { (mkApp u v , h) →
      cong (λ k → f (app u v) (mkApp u v , k))
           (funExt λ { true → refl ; false → refl }) }

    fun-UP : Iso (AppG A B ⊢ C) (A ⊢ (C ⟜ᵃ B))
    fun-UP .Iso.fun = fun-curry
    fun-UP .Iso.inv = fun-uncurry
    fun-UP .Iso.sec = fun-β
    fun-UP .Iso.ret = fun-η

  -- ================================================================
  -- 5.  SCOPES AND `Scoped`, AS THE GENERIC μ.
  --
  --     No bespoke datatype.  `Scoped` is `Ind.μ` at a description in
  --     the generic functor language, with the SCOPE as the nonterminal
  --     index.  The binder's action on the scope lives entirely in the
  --     index of the recursive occurrence.
  -- ================================================================

  Scope : Type₀
  Scope = List Name

  -- A scope IS a grammar over names -- and it is built from the INTERNAL
  -- connectives, not from `⊎`: the empty scope is `⊥G`, and extending is
  -- an internal `⊕` with a representable.  So `In Γ` is a term of the
  -- calculus and is eliminated by `⊕-E`/`⊥-E` like any other.
  In : Scope → NmG
  In []      = ⊥G
  In (m ∷ Γ) = ⌈ m ⌉ ⊕ In Γ

  -- nonterminals: one per scope, all at sort `tm`
  open Ind λSub ℓ-zero Scope (λ _ → tm) public

  data ScTag : Type₀ where
    tVar tApp tLam : ScTag

  -- THE GRAMMAR.  Three alternatives, one per operation of the theory.
  -- Note the binder: `⊕e Name` guesses the bound name, `⌜ ⌈ n ⌉ ⌝` pins
  -- the name slot to it (a representable AT SORT `nm`), and the body's
  -- nonterminal is `n ∷ Γ`.  The guess is uniquely determined by the
  -- representable, so the alternative stays unambiguous.
  ScopedF : Scope → Functor tm
  ScopedF Γ = ⊕e ScTag λ
    { tVar → ⊗e varOp (λ _ → ⌜ In Γ ⌝)
    ; tApp → ⊗e appOp (λ _ → Var Γ)
    ; tLam → ⊕e Name λ n → ⊗e lamOp (λ { true  → ⌜ ⌈ n ⌉ ⌝
                                       ; false → Var (n ∷ Γ) })
    }

  Scoped : Scope → TmG
  Scoped Γ t = μ ScopedF (Γ , t)

  -- ----------------------------------------------------------------
  -- PRIMITIVE.  The container encoding of `ScopedF`, respelled in the
  -- connectives.  This is the ONLY place the shape/position encoding is
  -- opened: `sc-roll`, `sc-unroll`, the three rules, the elaborator of
  -- §6 and the checker of §8 are all derived from it by composition.
  --
  -- Note what it does NOT do: it never matches on `Raw`, and it never
  -- looks inside a splitting -- `sp` is passed through abstractly.  All
  -- it does is rearrange tuples, which is why it is honest to call it a
  -- change of notation rather than a proof.
  -- ----------------------------------------------------------------

  Step : (Scope → TmG) → Scope → TmG
  Step M Γ =   VarG (In Γ)
             ⊕ (AppG (M Γ) (M Γ)
             ⊕ ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (M (n ∷ Γ))))

  ⟦Sc⟧ : {M : Ix → Type₀} (Γ : Scope)
       → ⟦ ScopedF Γ ⟧ M ⊢ Step (λ Δ x → M (Δ , x)) Γ
  ⟦Sc⟧ Γ _ ((tVar , sp , sh) , _) = inl (sp , λ a → lower (sh a))
  ⟦Sc⟧ Γ _ ((tApp , sp , _) , rc) =
    inr (inl (sp , λ { true → rc (true , tt*) ; false → rc (false , tt*) }))
  ⟦Sc⟧ Γ _ ((tLam , n , sp , sh) , rc) =
    inr (inr (n , sp , λ { true → lower (sh true) ; false → rc (false , tt*) }))

  ⟦Sc⟧⁻ : {M : Ix → Type₀} (Γ : Scope)
        → Step (λ Δ x → M (Δ , x)) Γ ⊢ ⟦ ScopedF Γ ⟧ M
  ⟦Sc⟧⁻ Γ _ (inl (sp , h)) =
    (tVar , sp , λ a → lift (h a)) , λ { (_ , ()) }
  ⟦Sc⟧⁻ Γ _ (inr (inl (sp , h))) =
    (tApp , sp , λ _ → tt*)
      , λ { (true , _) → h true ; (false , _) → h false }
  ⟦Sc⟧⁻ Γ _ (inr (inr (n , sp , h))) =
    (tLam , n , sp , λ { true → lift (h true) ; false → tt* })
      , λ { (true , ()) ; (false , _) → h false }

  -- `Scoped` is an algebra and a coalgebra for `Step`.  From here down,
  -- nothing matches.
  sc-unroll : (Γ : Scope) → Scoped Γ ⊢ Step Scoped Γ
  sc-unroll Γ = ⟦Sc⟧ Γ ∘g μ-coalg ScopedF Γ

  sc-roll : (Γ : Scope) → Step Scoped Γ ⊢ Scoped Γ
  sc-roll Γ = μ-alg ScopedF Γ ∘g ⟦Sc⟧⁻ Γ

  -- The three rules of the grammar: `roll` after a coproduct injection.
  -- Point-free, and derived -- not primitive.
  sc-var : (Γ : Scope) → VarG (In Γ) ⊢ Scoped Γ
  sc-var Γ = sc-roll Γ ∘g ⊕-I₁

  sc-app : (Γ : Scope) → AppG (Scoped Γ) (Scoped Γ) ⊢ Scoped Γ
  sc-app Γ = sc-roll Γ ∘g (⊕-I₂ ∘g ⊕-I₁)

  sc-lam : (Γ : Scope) (n : Name) → LamG ⌈ n ⌉ (Scoped (n ∷ Γ)) ⊢ Scoped Γ
  sc-lam Γ n = sc-roll Γ ∘g (⊕-I₂ ∘g (⊕-I₂ ∘g ⊕ᴰ-I Name n))

  -- ================================================================
  -- 6.  ELABORATION TO DE BRUIJN, AS THE GENERIC `fold`.
  --
  --     Motive `(Γ , t) ↦ DB (length Γ)`.  There is no `Maybe`:
  --     scope-correctness sits in the INDEX, so elaboration is total.
  -- ================================================================

  data DB : ℕ → Type₀ where
    dvar : ∀ {k} → Fin k → DB k
    dapp : ∀ {k} → DB k → DB k → DB k
    dlam : ∀ {k} → DB (suc k) → DB k

  -- a constant grammar is a constant: the unique map into `λ _ → X`
  constG : {s : LSort} {A : TheoryTy ℓ-zero s} {X : Type₀}
         → X → A ⊢ (λ _ → X)
  constG x _ _ = x

  -- Reading a de Bruijn index off a scope membership: `⊥-E` at the
  -- empty scope, `⊕-E` at an extension.  Note the hit branch discards
  -- the representable rather than eliminating it with `⌈⌉-E`: `⌈⌉-E`
  -- matches `Eq.refl`, and the witness here comes from `Discrete Name`
  -- via `pathToEq`, which does not reduce to `Eq.refl` in cubical.  The
  -- index is determined by the POSITION in the scope, not by the proof,
  -- so nothing is lost -- and the tests below only compute because of
  -- it.  This is the `Eq`-vs-`transp` trap, one level down.
  toIx : (Γ : Scope) → In Γ ⊢ (λ _ → Fin (length Γ))
  toIx []      = ⊥-E
  toIx (m ∷ Γ) = ⊕-E (constG fzero ∘g ⊤-I) ((λ _ → fsuc) ∘g toIx Γ)

  Mot : Ix → Type₀
  Mot (Γ , _) = DB (length Γ)

  -- The algebra is `⟦Sc⟧` followed by the elimination rules of §3, one
  -- per alternative -- `⊕-E`/`⊕ᴰ-E` from `TheoryGrammar.Rules`.  No
  -- clause of the fold looks at a term or at a shape.
  dbStep : (Γ : Scope) → Step (λ Δ _ → DB (length Δ)) Γ ⊢ (λ _ → DB (length Γ))
  dbStep Γ = ⊕-E (var-elim λ n i → dvar (toIx Γ n i))
            (⊕-E (app-elim λ _ _ a b → dapp a b)
                    (⊕ᴰ-E λ _ → lam-elim λ _ _ _ d → dlam d))

  toDB : (Γ : Scope) → Scoped Γ ⊢ (λ _ → DB (length Γ))
  toDB Γ t d = fold Mot alg (Γ , t) d
    where
    alg : (Γ' : Scope) (t' : Raw) (sh : Sh (ScopedF Γ') t')
        → ((p : Pos (ScopedF Γ') t' sh) → Mot (nx (ScopedF Γ') t' sh p))
        → Mot (Γ' , t')
    alg Γ' t' sh rc = dbStep Γ' t' (⟦Sc⟧ {M = Mot} Γ' t' (sh , rc))

  -- ================================================================
  -- 7.  GRADING: EVERY SPLITTING OF THIS SUBSTRATE IS PROPER.
  --
  --     Grade a name 0 and a term by its node count.  Then every slot
  --     of every splitting is STRICTLY smaller than the whole -- for
  --     the `nm` slots trivially, since a term has at least one node.
  --     So the guardedness side condition that a general substrate
  --     would have to discharge per description is discharged here ONCE,
  --     for the substrate; every description over it is well-founded,
  --     and §8's checker is a hylo with no side condition to check.
  -- ================================================================

  size : Raw → ℕ
  size (var _)   = 1
  size (app u v) = suc (size u + size v)
  size (lam _ t) = suc (size t)

  grade : (s : LSort) → Carrier s → ℕ
  grade nm _ = 0
  grade tm t = size t

  proper : (o : LOp) (t : Raw) (sp : LSplit o t) (a : LAr o)
         → grade (LSortOf o a) (LParts o t sp a) < size t
  proper varOp _ (mkVar n)   _     = ≤-refl
  proper appOp _ (mkApp u v) true  = suc-≤-suc ≤SumLeft
  proper appOp _ (mkApp u v) false = suc-≤-suc ≤SumRight
  proper lamOp _ (mkLam n t) true  = suc-≤-suc zero-≤
  proper lamOp _ (mkLam n t) false = suc-≤-suc ≤-refl

  -- the recursor the grading buys: structural recursion on the grade,
  -- with the term never matched.  `go` recurses on the FUEL, so this
  -- reduces on closed terms (§9), unlike an accessibility argument.
  recSize : {M : Raw → Type₀}
          → ((t : Raw) → ((s : Raw) → size s < size t → M s) → M t)
          → (t : Raw) → M t
  recSize {M} f t = go (suc (size t)) t ≤-refl
    where
    go : (k : ℕ) (s : Raw) → size s < k → M s
    go zero    s p = E.rec (¬-<-zero p)
    go (suc k) s p = f s λ r q → go k r (≤-trans q (pred-≤-pred p))

  -- ================================================================
  -- 8.  DECIDABILITY -- ALL OF IT INHERITED.
  --
  --     Nothing about decisions is lambda-specific, so nothing about
  --     decisions is defined here.  `TheoryGrammar.Decidable` carries
  --     the whole theory generically:
  --
  --       ¬G A = A ⇒ ⊥G, and a decision is a map `⊤ ⊢ A ⊕ A'` for a
  --       complement A' -- `Dec⟨ A ⟩` is the default A' = ¬G A;
  --       `&-swap`, `contra`, `dist&`, `¬G-map`, `deMorgan`;
  --       `dec-map`, `dec-⊕`, `dec-&`, `dec-⊤`, `dec-⊥`;
  --       `⊗-miss`, `⊗-thin`, `⊗-refute`, `dec-⊗`.
  --
  --     All of it is composed out of `Rules`' intro/elim; the additive
  --     half needs only a `Model`, the tensor half a `Substrate` plus a
  --     `DecReadable`.  What this instance owes is exactly that record:
  --     three substrate facts, below.
  -- ================================================================

  -- PRIMITIVE (substrate).  At most one splitting: unique readability.
  Split-isProp : (o : LOp) (t : Raw) (p q : LSplit o t) → p ≡ q
  Split-isProp varOp _ (mkVar _)   (mkVar _)   = refl
  Split-isProp appOp _ (mkApp _ _) (mkApp _ _) = refl
  Split-isProp lamOp _ (mkLam _ _) (mkLam _ _) = refl

  -- `⊗-refute` -- refuting one slot at its own part refutes the whole
  -- tensor -- is derived generically from uniqueness alone.
  open Precise Split-isProp public

  -- PRIMITIVE (substrate).  Decidable unique readability, stated
  -- internally: for each operation, every term either is an o-node or
  -- carries an internal refutation of being one.
  ⊗-decSplit : (o : LOp) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
  ⊗-decSplit varOp (var n)   _ = dec-yes (⊗ˢ varOp (λ _ → ⊤G)) (var n)   (mkVar n , λ _ → tt)
  ⊗-decSplit varOp (app u v) _ = dec-no  (⊗ˢ varOp (λ _ → ⊤G)) (app u v) λ { (() , _) }
  ⊗-decSplit varOp (lam n b) _ = dec-no  (⊗ˢ varOp (λ _ → ⊤G)) (lam n b) λ { (() , _) }
  ⊗-decSplit appOp (var n)   _ = dec-no  (⊗ˢ appOp (λ _ → ⊤G)) (var n)   λ { (() , _) }
  ⊗-decSplit appOp (app u v) _ = dec-yes (⊗ˢ appOp (λ _ → ⊤G)) (app u v) (mkApp u v , λ _ → tt)
  ⊗-decSplit appOp (lam n b) _ = dec-no  (⊗ˢ appOp (λ _ → ⊤G)) (lam n b) λ { (() , _) }
  ⊗-decSplit lamOp (var n)   _ = dec-no  (⊗ˢ lamOp (λ _ → ⊤G)) (var n)   λ { (() , _) }
  ⊗-decSplit lamOp (app u v) _ = dec-no  (⊗ˢ lamOp (λ _ → ⊤G)) (app u v) λ { (() , _) }
  ⊗-decSplit lamOp (lam n b) _ = dec-yes (⊗ˢ lamOp (λ _ → ⊤G)) (lam n b) (mkLam n b , λ _ → tt)

  -- PRIMITIVE (signature).  Slotwise decisions combine.  This is where
  -- FINITENESS of the arity is used -- for an infinite arity the
  -- statement is false, which is why `Decidable` takes it as a field --
  -- and it is the one place a sum is eliminated at a slot's index
  -- rather than at the whole's.  It matches on the OPERATION, never on
  -- a term.
  λ-decSlots : (o : LOp) (A : (a : LAr o) → TheoryTy ℓ-zero (LSortOf o a))
               (t : Raw) (sp : LSplit o t)
             → ((a : LAr o) → Dec⟨ A a ⟩ (LParts o t sp a))
             → Dec⟨ ⊗ˢ o A ⟩ t
  λ-decSlots varOp A t sp h with h tt
  ... | inl x = dec-yes (⊗ˢ varOp A) t (sp , λ _ → x)
  ... | inr k = dec-no  (⊗ˢ varOp A) t (⊗-refute varOp tt A t sp k)
  λ-decSlots appOp A t sp h with h true | h false
  ... | inr k | _     = dec-no  (⊗ˢ appOp A) t (⊗-refute appOp true  A t sp k)
  ... | inl x | inr k = dec-no  (⊗ˢ appOp A) t (⊗-refute appOp false A t sp k)
  ... | inl x | inl y = dec-yes (⊗ˢ appOp A) t (sp , λ { true → x ; false → y })
  λ-decSlots lamOp A t sp h with h true | h false
  ... | inr k | _     = dec-no  (⊗ˢ lamOp A) t (⊗-refute lamOp true  A t sp k)
  ... | inl x | inr k = dec-no  (⊗ˢ lamOp A) t (⊗-refute lamOp false A t sp k)
  ... | inl x | inl y = dec-yes (⊗ˢ lamOp A) t (sp , λ { true → x ; false → y })

  -- the three facts, packaged; `dec-⊗` follows generically
  λDR : DecReadable λSub ℓ-zero
  λDR .splitProp = Split-isProp
  λDR .decSplit  = ⊗-decSplit
  λDR .decSlots  = λ-decSlots

  open DecTensor λDR public using (dec-⊗)

  -- ================================================================
  -- 9.  THE BINDER: YONEDA, AND ITS DECISION.
  --
  --     The one connective this instance owes that the generic layer
  --     cannot supply, because it is about a DEPENDENT tensor: the
  --     body's grammar depends on the name in the binder slot.
  -- ================================================================

  -- PRIMITIVE.  Guessing the bound name with `⊕ᴰ Name` and pinning it
  -- with the representable `⌈ n ⌉` is the same as reading it off the
  -- splitting.  This is `⌈⌉-UP` in the shape the checker needs, and the
  -- only `Eq.refl` match in the file.
  LamGᵈ : (Name → TmG) → TmG
  LamGᵈ A t =
    Σ[ sp ∈ IsLam t ] A (LParts lamOp t sp true) (LParts lamOp t sp false)

  collapse : {A : Name → TmG} → ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (A n)) ⊢ LamGᵈ A
  collapse _ (n , sp , h) with h true
  ... | Eq.refl = sp , h false

  collapse⁻ : {A : Name → TmG} → LamGᵈ A ⊢ ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (A n))
  collapse⁻ t (sp , a) =
    LParts lamOp t sp true , sp , λ { true → Eq.refl ; false → a }

  -- and its decision, exactly parallel to the generic `dec-⊗`
  private
    decLam : (A : Name → TmG) (t : Raw) (sp : IsLam t)
           → Dec⟨ A (LParts lamOp t sp true) ⟩ (LParts lamOp t sp false)
           → Dec⟨ LamGᵈ A ⟩ t
    decLam A t sp (inl a) = dec-yes (LamGᵈ A) t (sp , a)
    decLam A t sp (inr k) = dec-no  (LamGᵈ A) t λ x →
      k (subst (λ s → A (LParts lamOp t s true) (LParts lamOp t s false))
               (Split-isProp lamOp t (x .fst) sp) (x .snd))

  dec-lamᵈ : (A : Name → TmG) (t : Raw)
           → ((sp : IsLam t)
              → Dec⟨ A (LParts lamOp t sp true) ⟩ (LParts lamOp t sp false))
           → Dec⟨ LamGᵈ A ⟩ t
  dec-lamᵈ A t d with ⊗-decSplit lamOp t tt
  ... | inl x = decLam A t (x .fst) (d (x .fst))
  ... | inr k = dec-no (LamGᵈ A) t λ y → k (y .fst , λ _ → tt)

  -- ================================================================
  -- 10.  THE SCOPE CHECKER.
  --
  --      Its statement is a map of the calculus:
  --
  --          ⊤ ⊢ &ᴰ Scope (λ Δ → Scoped Δ ⊕ ¬G (Scoped Δ))
  --
  --      "for every term and every scope, a scoping derivation or a
  --      refutation".  Decide in EVERY scope at once, then instantiate
  --      at `[]` with `&ᴰ-E`; the quantification is forced, because the
  --      scope grows while the term shrinks.
  --
  --      The algorithm: unfold one step (`sc-unroll`), decide the three
  --      summands, recombine with `dec-⊕`, fold back (`sc-roll`).  The
  --      recursive calls sit at `LParts o t sp a` and `proper` is
  --      exactly the descent proof `recSize` asks for.
  -- ================================================================

  -- Decidability of a representable at sort `nm`.  This is the ONE place
  -- the external `Discrete Name` is used, and it is used to BUILD an
  -- internal map, never to case-split on one -- which is the whole rule
  -- for how external decidability may enter the calculus.
  dec-⌈⌉ : (m : Name) → ⊤G ⊢ Dec⟨ ⌈_⌉ {s = nm} m ⟩
  dec-⌈⌉ m n _ with n ≟ m
  ... | yes p = dec-yes (⌈_⌉ {s = nm} m) n (Eq.pathToEq p)
  ... | no ¬p = dec-no  (⌈_⌉ {s = nm} m) n λ e → E.rec (¬p (Eq.eqToPath e))

  -- Membership in a scope is decidable, by induction on the scope and
  -- nothing else: `⊥`'s rule at the empty scope, `dec-⊕` at the cons.
  dec-In : (Γ : Scope) → ⊤G ⊢ Dec⟨ In Γ ⟩
  dec-In []      = dec-no (In []) ∘g ⇒-I &-E₂
  dec-In (m ∷ Γ) = dec-⊕ ⌈ m ⌉ (In Γ) ∘g &-I (dec-⌈⌉ m) (dec-In Γ)

  DecScoped : TmG
  DecScoped = &ᴰ Scope (λ Δ → Dec⟨ Scoped Δ ⟩)

  check : ⊤G ⊢ DecScoped
  check t _ = recSize {M = DecScoped} step t
    where
    step : (t : Raw)
           → ((s : Raw) → size s < size t → DecScoped s) → DecScoped t
    step t rec Δ =
      dec-map (Step Scoped Δ) (Scoped Δ) (sc-roll Δ) (sc-unroll Δ) t dStep
      where
      Vr Ap Lm : TmG
      Vr = VarG (In Δ)
      Ap = AppG (Scoped Δ) (Scoped Δ)
      Lm = ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (Scoped (n ∷ Δ)))

      -- the recursive call, with `&ᴰ` eliminated at the scope we need
      rec' : (s : Raw) → size s < size t → (Δ' : Scope) → Dec⟨ Scoped Δ' ⟩ s
      rec' s p Δ' = &ᴰ-E Scope {B = λ Δ'' → Dec⟨ Scoped Δ'' ⟩} Δ' s (rec s p)

      dVar : Dec⟨ Vr ⟩ t
      dVar = dec-⊗ varOp (λ _ → In Δ) t λ sp a →
               dec-In Δ (LParts varOp t sp a) tt

      dApp : Dec⟨ Ap ⟩ t
      dApp = dec-⊗ appOp (λ b → if b then Scoped Δ else Scoped Δ) t λ sp →
               λ { true  → rec' _ (proper appOp t sp true)  Δ
                 ; false → rec' _ (proper appOp t sp false) Δ }

      dLam : Dec⟨ Lm ⟩ t
      dLam = dec-map (LamGᵈ (λ n → Scoped (n ∷ Δ))) Lm collapse⁻ collapse t
               (dec-lamᵈ (λ n → Scoped (n ∷ Δ)) t λ sp →
                  rec' _ (proper lamOp t sp false) (LParts lamOp t sp true ∷ Δ))

      dStep : Dec⟨ Step Scoped Δ ⟩ t
      dStep = dec-⊕ Vr (Ap ⊕ Lm) t (dVar , dec-⊕ Ap Lm t (dApp , dLam))

  -- instantiate the `&ᴰ` at the empty scope: closedness
  closed? : ⊤G ⊢ Dec⟨ Scoped [] ⟩
  closed? = &ᴰ-E Scope [] ∘g check

-- ==================================================================
-- 11.  IT COMPUTES.  Each `refl` holds only if the whole pipeline --
--      `check`, the generic `μ`'s `sup`, `fold`, `toIx` -- reduces.
--      Note the tests too are stated internally: the observation is a
--      `⊕-E` into a constant grammar, not a match on a `Dec`.
-- ==================================================================

module Test where

  open import Cubical.Data.Nat using (discreteℕ)
  open Lam ℕ discreteℕ

  idT open' bigger shadow : Raw
  idT    = lam 0 (var 0)                                -- λx. x
  open'  = lam 0 (var 1)                                -- λx. y
  bigger = app (lam 0 (var 0)) (lam 1 (lam 2 (var 1)))  -- (λx.x)(λy.λz.y)
  shadow = lam 0 (lam 0 (var 0))                        -- λx. λx. x

  -- OBSERVING a decision.  Not a match on `Dec`: an `⊕-E` into the
  -- constant grammar `λ _ → Bool`, i.e. an ordinary semantic action out
  -- of the internal sum.
  closed! : ⊤G ⊢ (λ _ → Bool)
  closed! = ⊕-E {A = Scoped []} {C = λ _ → Bool} {B = ¬G (Scoped [])}
                (λ _ _ → true) (λ _ _ → false) ∘g closed?

  _ : closed! idT    tt ≡ true
  _ = refl

  _ : closed! open'  tt ≡ false
  _ = refl

  _ : closed! bigger tt ≡ true
  _ = refl

  _ : closed! shadow tt ≡ true
  _ = refl

  -- Elaboration.  `Maybe` is a metalanguage type, so it is spelled
  -- internally: the target is `(λ _ → DB 0) ⊕ ⊤G`, and the two branches
  -- are `⊕-I₁ ∘ toDB` and `⊕-I₂ ∘ ⊤-I`.  The whole pipeline --
  -- `check`, `sc-roll`/`sc-unroll`, `fold`, `toIx` -- is one composite
  -- morphism `⊤ ⊢ (λ _ → DB 0) ⊕ ⊤`.
  DBG : TmG
  DBG _ = DB 0

  elab : ⊤G ⊢ (DBG ⊕ ⊤G)
  elab = ⊕-E (⊕-I₁ ∘g toDB []) (⊕-I₂ ∘g ⊤-I) ∘g closed?

  -- the two expected outcomes, as introduction rules
  some : (t : Raw) → DB 0 → (DBG ⊕ ⊤G) t
  some = ⊕-I₁ {A = DBG} {B = ⊤G}

  none : (t : Raw) → (DBG ⊕ ⊤G) t
  none t = ⊕-I₂ {B = ⊤G} {A = DBG} t tt

  _ : elab idT tt ≡ some idT (dlam (dvar fzero))
  _ = refl

  _ : elab shadow tt ≡ some shadow (dlam (dlam (dvar fzero)))
  _ = refl

  _ : elab bigger tt
        ≡ some bigger (dapp (dlam (dvar fzero))
                            (dlam (dlam (dvar (fsuc fzero)))))
  _ = refl

  _ : elab open' tt ≡ none open'
  _ = refl
