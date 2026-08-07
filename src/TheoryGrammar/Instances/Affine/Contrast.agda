{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  LINEAR ⊂ AFFINE ⊂ CARTESIAN, machine-checked.

  This is the ONLY file in `Instances/Affine/` that mentions `LinLam`.
  It is separated for two reasons: the linear side is another agent's,
  so nothing load-bearing should depend on it; and the comparison is
  genuinely a different subject from the affine promodel itself.

  What it does:

    * `lin→aff`      -- every linear splitting is affine, and
      `lin⊊aff`      -- STRICTLY: `adrop` is not one.
                        Together with `Base.aff→cart` / `Base.aff⊊cart`
                        this is the chain, each link one constructor.

    * `linTm→aff`    -- the term-level inclusion: every linear term is
                        an affine term at the same usage.  A `⊢`-map of
                        grammars, so it neither invents nor discards a
                        variable.

    * `noWkLin`      -- the WEAKENING row of the table, refuted on the
                        linear side.  `Base.wkUnit` proves
                        `⊤G ⊢ 𝟙 ⊛ 𝟙` affinely; here the corresponding
                        linear grammar is EMPTY at any usage that owns
                        anything, because `Use⊎` with both slots
                        `Empty` forces the whole `Empty`.  This is the
                        internal, `⊗ˢ`-level statement of "linear logic
                        has no weakening", and it is not a remark about
                        the syntax.

    * `linDeadVacuous`, `linDceUnique`
                     -- the DEAD-CODE row on the linear side, by
                        citation rather than paraphrase: they ARE
                        `Opt.deadBinder` and `Opt.dceUnique`.  Put
                        beside `Dead.noDeadEmpty` and
                        `Dead.dceNotUnique` the row is complete, both
                        cells checked.

    * `noLinearK`    -- and the concrete separation: no closed LINEAR
                        term has the occurrence profile of
                        `Syntax.constAff` (`λx.λy.x`), because
                        `Opt.budgetEq` at the empty usage says a closed
                        linear term has as many occurrences as binders,
                        and K has one and two.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Affine.Contrast where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Affine.Dead public

-- the linear development, qualified: nothing from it is re-exported
import TheoryGrammar.Instances.LinLam.Opt as Opt

-- ==================================================================
-- §1  THE INCLUSION OF PROMODELS.
-- ==================================================================

lin→aff : ∀ {u v w} → Opt.Use⊎ u v w → Aff⊎ u v w
lin→aff Opt.unil       = anil
lin→aff (Opt.uleft s)  = aleft  (lin→aff s)
lin→aff (Opt.uright s) = aright (lin→aff s)
lin→aff (Opt.uskip s)  = askip  (lin→aff s)

-- ... and it is STRICT.  `adrop` -- a variable the whole owns and
-- neither premise claims -- is not a linear splitting.
lin⊊aff : Aff⊎ (false ∷ []) (false ∷ []) (true ∷ [])
        × (Opt.Use⊎ (false ∷ []) (false ∷ []) (true ∷ []) → ⊥)
lin⊊aff = adrop anil , λ ()

-- ==================================================================
-- §1.5  THE CONTRACTION ROW, both cells, by citation.  Affinity did
-- NOT restore the (true,true) clause, so the linear theorem and the
-- affine one are the same theorem twice.
-- ==================================================================

linNoDup : (u : Usage) → Opt.Use⊎ (true ∷ u) (true ∷ u) (true ∷ u) → ⊥
linNoDup = Opt.noDupUse

affNoDup : (u : Usage) → Aff⊎ (true ∷ u) (true ∷ u) (true ∷ u) → ⊥
affNoDup = noDupAff

-- ... and affinely the SHARPER form, which `LinLam` does not state:
-- only a dead usage splits as itself, with no hypothesis at all.
_ : ∀ {u w} → Aff⊎ u u w → Empty u
_ = affDiag

-- ==================================================================
-- §2  THE INCLUSION OF TERMS.
--
-- `Opt.Empty`/`Opt.Solo` and `Base.Empty`/`Base.Solo` are the same
-- definitions written twice (the affine directory is deliberately
-- self-contained), so the bridges are pure recursion with no content.
-- ==================================================================

emptyL→A : (u : Usage) → Opt.Empty u → Empty u
emptyL→A []          e = tt
emptyL→A (true  ∷ u) e = E.rec e
emptyL→A (false ∷ u) e = emptyL→A u e

soloL→A : (u : Usage) → Opt.Solo u → Solo u
soloL→A []          s = E.rec s
soloL→A (true  ∷ u) s = emptyL→A u s
soloL→A (false ∷ u) s = soloL→A u s

-- THEOREM.  Every linear term is an affine term AT THE SAME USAGE.
-- The index is preserved, so this map cannot silently rebalance
-- ownership; it really is an inclusion of calculi.
linTm→aff : ∀ {u} → Opt.Tm u → ATm u
linTm→aff (Opt.tvar {u} s)   = tvar (soloL→A u s)
linTm→aff (Opt.tapp s a b)   = tapp (lin→aff s) (linTm→aff a) (linTm→aff b)
linTm→aff (Opt.tlam b)       = tlam (linTm→aff b)

linTmG→aff : (u : Usage) → Opt.Tm u → ATm u
linTmG→aff u = linTm→aff

-- the linear identity really does land on the affine one
_ : linTm→aff Opt.idLin ≡ idAff
_ = refl

-- ==================================================================
-- §3  THE WEAKENING ROW, refuted linearly.
--
-- `Base.wkUnit : ⊤G ⊢ 𝟙 ⊛ 𝟙` is the affine statement that anything may
-- be discarded.  Linearly the same grammar is empty wherever anything
-- is owned, and the reason is one lemma: a `Use⊎` with two `Empty`
-- slots has an `Empty` whole.  (`adrop` is exactly the constructor
-- that breaks it, which is why `Base.affDropAll` exists.)
-- ==================================================================

-- PRIMITIVE (phase 1)
linUnitEmpty : ∀ {u₁ u₂ u} → Opt.Use⊎ u₁ u₂ u
             → Opt.Empty u₁ → Opt.Empty u₂ → Opt.Empty u
linUnitEmpty Opt.unil       e₁ e₂ = tt
linUnitEmpty (Opt.uleft s)  e₁ e₂ = E.rec e₁
linUnitEmpty (Opt.uright s) e₁ e₂ = E.rec e₂
linUnitEmpty (Opt.uskip s)  e₁ e₂ = linUnitEmpty s e₁ e₂

-- THEOREM.  LINEAR LOGIC HAS NO WEAKENING, internally.
noWkLin : (Opt.⊤G {tt} Opt.⊢ (Opt.nothingLeft Opt.⊛ Opt.nothingLeft)) → ⊥
noWkLin f =
  linUnitEmpty (w .fst .snd .snd) (w .snd true .fst) (w .snd false .fst)
  where
  w : (Opt.nothingLeft Opt.⊛ Opt.nothingLeft) (true ∷ [])
  w = f (true ∷ []) tt

-- ... beside the affine one, which is a term
_ : ⊤G ⊢ (𝟙 ⊛ 𝟙)
_ = wkUnit

-- ==================================================================
-- §4  THE DEAD-CODE ROW, both cells.
--
-- The linear cells are CITATIONS, not paraphrases: these are literally
-- `Opt`'s theorems, typechecked here so the table cannot drift.
-- ==================================================================

linDeadVacuous : Opt.DeadBinder Opt.⊢ Opt.⊥G
linDeadVacuous = Opt.deadBinder

linDceUnique : (f g : Opt.DeadBinder Opt.⊢ Opt.TmG) → f ≡ g
linDceUnique = Opt.dceUnique

-- affinely, both are FALSE
_ : (DeadBinder ⊢ ⊥G) → ⊥
_ = noDeadEmpty

_ : ((f g : DeadBinder ⊢ ATmG) → f ≡ g) → ⊥
_ = dceNotUnique

-- ==================================================================
-- §5  THE CONCRETE SEPARATION: K IS NOT LINEAR.
--
-- `Opt.budgetEq` says `occ t ≡ live u + lam t`.  At the empty usage
-- that is `occ ≡ lam`: a closed linear term has exactly as many
-- variable occurrences as it has binders.  `Syntax.constAff` has one
-- and two.
-- ==================================================================

linClosedBalanced : (t : Opt.Tm []) → Opt.occOf t ≡ Opt.lamOf t
linClosedBalanced t = Opt.budgetEq t

noLinearK : (t : Opt.Tm [])
          → Opt.occOf t ≡ occOf constAff
          → Opt.lamOf t ≡ lamOf constAff
          → ⊥
noLinearK t eo el = znots (injSuc (sym eo ∙ linClosedBalanced t ∙ el))
