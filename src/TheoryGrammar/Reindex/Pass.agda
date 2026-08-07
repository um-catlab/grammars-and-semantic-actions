{-
  A VERIFIED PASS, AND A CHAIN OF THEM.

  A compiler is not one map of theories, it is a SEQUENCE, and each link
  crosses a signature:

      unicode monoid  →  token monoid  →  AST  →  linear usages  →  heap

  Each arrow lands in a slightly richer theory and retains enough data to
  project back.  `Reindex.Base` supplies the link; this file supplies the
  spine, and its content is entirely the answer to one question:

      WHICH OF THE THREE DATA OF A LINK SURVIVE COMPOSITION?

  The answer is all three, and they survive independently:

      SigMor              always -- `_⨟σ_`
      ReindexOver         always -- `_⨟r_`
      SplitPresAtOver     `presComp`, needs both links
      ReflectsSplitAtOver `reflComp`, needs both links
      ArSection           `compArSection`

  so a `Pass` (sig + map + preservation everywhere) composes, and a
  `Reflective` pass composes with a `Reflective` pass.

  --------------------------------------------------------------------
  WHY REFLECTION IS OPTIONAL, AND WHAT IS LOST WITHOUT IT.

  A pass that PRESERVES splittings maps a source decomposition to a
  target one: `push⊗O` -- "the code emitted for a compound is the
  compound of the code emitted for the pieces".  A pass that also
  REFLECTS them inverts that: `pull⊗O` -- "every decomposition of the
  emitted object comes from one of the source, uniquely enough".  It is
  the discrete Conduche condition, and it is what "project back to an
  earlier pass" MEANS at the level of the multiplicative fragment: with
  it, a fact proved downstream transports upstream (`Codegen.layFrame`,
  `Codegen.noDupLay`); without it only the additive fragment does.

  Both halves genuinely fail in practice, at different operations, and
  the framework's job is to say WHERE:

      `Codegen.layPres`/`layRefl`  -- the non-compacting layout: BOTH
                                      hold, at BOTH operations.
      `Codegen.noPackPres`         -- the compacting layout: preservation
                                      FAILS at `appop`.
      `Scope.¬presLam`/`¬reflLam`  -- named → de Bruijn: BOTH fail, at
                                      `lamOp` only.
      `Reindex.LinLam.¬presApp`    -- AST → usages: preservation fails at
                                      `appOp`, and its failure AT A POINT
                                      is exactly non-linearity.

  So `Pass` demands preservation everywhere and leaves reflection to a
  separate record.  A chain of passes composes; a chain of REFLECTIVE
  passes composes reflectively, which is the theorem that decides
  whether the back-projection reaches across a whole compiler or only
  one link.  `chainReflective` is that theorem.

  --------------------------------------------------------------------
  ON LEVELS.  `Pass` is heterogeneous: source and target may sit at
  different levels, which is necessary (a glued promodel is at the max of
  its factors').  `Chain`, being a list, is homogeneous -- a chain whose
  theories change level has to be built with `_⨟P_` by hand.  That is a
  limitation of Agda's lists, not of the notion.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Reindex.Pass where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.ChangeOfTheory using (SigMor; onSort; onOp; onAr)
open import TheoryGrammar.Reindex.Base

private variable
  ℓS ℓS' ℓS'' ℓ ℓ' ℓ2 ℓ2' ℓ3 ℓ3' : Level
  ℓX ℓX' ℓX'' ℓP ℓP' ℓP'' : Level

-- ==================================================================
-- A THEORY: a signature together with a promodel of it.  Bundled ONLY
-- so that a chain can be a list; every construction below could be
-- written unbundled.
-- ==================================================================

record Theory ℓS ℓ ℓ' ℓX ℓP
  : Type (ℓ-max (ℓ-suc ℓS) (ℓ-max (ℓ-suc ℓ)
          (ℓ-max (ℓ-suc ℓ') (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓP))))) where
  field
    {Sorts} : Type ℓS
    sig     : SortedSig Sorts ℓ ℓ'
    fib     : Fibered sig ℓX ℓP

open Theory public

theory : {S : Type ℓS} (σ : SortedSig S ℓ ℓ') → Fibered σ ℓX ℓP
       → Theory ℓS ℓ ℓ' ℓX ℓP
theory σ F .Sorts = _
theory σ F .sig   = σ
theory σ F .fib   = F

-- ==================================================================
-- A PASS.  Source theory, target theory, the signature morphism, the
-- carrier map, and preservation at EVERY operation.  Reflection is NOT
-- here -- see the header.
-- ==================================================================

record Pass (T : Theory ℓS ℓ ℓ' ℓX ℓP) (U : Theory ℓS' ℓ2 ℓ2' ℓX' ℓP')
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓS' (ℓ-max ℓ2 (ℓ-max ℓ2'
          (ℓ-max ℓX (ℓ-max ℓX' (ℓ-max ℓP ℓP'))))))))) where
  field
    sigOf  : SigMor (T .sig) (U .sig)
    mapOf  : ReindexOver sigOf (T .fib) (U .fib)
    presOf : (o : T .sig .ops) → SplitPresAtOver mapOf o

open Pass public

-- ==================================================================
-- A BRIDGE: the same thing with NO verification -- a signature morphism
-- and a carrier map over it.  Bridges always compose; a `Pass` is a
-- bridge one has PAID for.  The distinction is not bureaucratic: the
-- AST → linear-usage bridge of `Reindex.LinLam` is a genuine bridge
-- whose preservation fails at `appOp`, and the linearity checker is
-- exactly the term-by-term decision of whether it is a pass there.
-- ==================================================================

record Link (T : Theory ℓS ℓ ℓ' ℓX ℓP) (U : Theory ℓS' ℓ2 ℓ2' ℓX' ℓP')
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓS' (ℓ-max ℓ2 (ℓ-max ℓ2'
          (ℓ-max ℓX ℓX'))))))) where
  field
    sigL : SigMor (T .sig) (U .sig)
    mapL : ReindexOver sigL (T .fib) (U .fib)

open Link public

-- a pass, with its verification forgotten
forget : {T : Theory ℓS ℓ ℓ' ℓX ℓP} {U : Theory ℓS' ℓ2 ℓ2' ℓX' ℓP'}
       → Pass T U → Link T U
forget P .sigL = P .sigOf
forget P .mapL = P .mapOf

-- REFLECTION, as a separate structure over a pass.  `secOf` is the
-- slot-section that `pull⊗O` needs and that the single-signature theory
-- never had to mention.
record Reflective {T : Theory ℓS ℓ ℓ' ℓX ℓP} {U : Theory ℓS' ℓ2 ℓ2' ℓX' ℓP'}
                  (P : Pass T U)
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ2' (ℓ-max ℓX (ℓ-max ℓX' (ℓ-max ℓP ℓP'))))))
  where
  field
    reflectsAt : (o : T .sig .ops) → ReflectsSplitAtOver (P .mapOf) o
    secOf      : (o : T .sig .ops) → ArSection (P .sigOf) o

open Reflective public

-- ==================================================================
-- THE IDENTITY PASS, and it reflects.
-- ==================================================================

idPass : (T : Theory ℓS ℓ ℓ' ℓX ℓP) → Pass T T
idPass T .sigOf  = idSigMor (T .sig)
idPass T .mapOf  = idReindexOver (T .fib)
idPass T .presOf = idPres (T .fib)

idReflective : (T : Theory ℓS ℓ ℓ' ℓX ℓP) → Reflective (idPass T)
idReflective T .reflectsAt = idReflects (T .fib)
idReflective T .secOf      = idArSection (T .sig)

-- ==================================================================
-- COMPOSITION.  THE SPINE.
-- ==================================================================

module _ {T : Theory ℓS ℓ ℓ' ℓX ℓP} {U : Theory ℓS' ℓ2 ℓ2' ℓX' ℓP'}
         {V : Theory ℓS'' ℓ3 ℓ3' ℓX'' ℓP''} where

  infixl 6 _⨟P_ _⨟L_

  _⨟L_ : Link T U → Link U V → Link T V
  (F ⨟L G) .sigL = F .sigL ⨟σ G .sigL
  (F ⨟L G) .mapL = F .mapL ⨟r G .mapL

  _⨟P_ : Pass T U → Pass U V → Pass T V
  (P ⨟P Q) .sigOf    = P .sigOf ⨟σ Q .sigOf
  (P ⨟P Q) .mapOf    = P .mapOf ⨟r Q .mapOf
  (P ⨟P Q) .presOf o =
    presComp (P .mapOf) (Q .mapOf) o
             (P .presOf o) (Q .presOf (P .sigOf .onOp o))

  -- ... AND REFLECTION COMPOSES WITH IT.  This is the fact the whole
  -- pipeline turns on: back-projection is not a one-link property.
  _⨟R_ : {P : Pass T U} {Q : Pass U V}
       → Reflective P → Reflective Q → Reflective (P ⨟P Q)
  _⨟R_ {P = P} {Q} RP RQ .reflectsAt o =
    reflComp (P .mapOf) (Q .mapOf) o
             (RP .reflectsAt o) (RQ .reflectsAt (P .sigOf .onOp o))
  _⨟R_ {P = P} {Q} RP RQ .secOf o =
    compArSection (P .sigOf) (Q .sigOf) o
                  (RP .secOf o) (RQ .secOf (P .sigOf .onOp o))

-- ==================================================================
-- A CHAIN OF PASSES, and its composite.
-- ==================================================================

data Chain {ℓS ℓ ℓ' ℓX ℓP}
  : Theory ℓS ℓ ℓ' ℓX ℓP → Theory ℓS ℓ ℓ' ℓX ℓP
  → Type (ℓ-max (ℓ-suc ℓS) (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ')
          (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓP))))) where
  done : {T : Theory ℓS ℓ ℓ' ℓX ℓP} → Chain T T
  _◅_  : {T U V : Theory ℓS ℓ ℓ' ℓX ℓP}
       → Pass T U → Chain U V → Chain T V

infixr 5 _◅_

composite : {T U : Theory ℓS ℓ ℓ' ℓX ℓP} → Chain T U → Pass T U
composite {T = T} done  = idPass T
composite (P ◅ c)       = P ⨟P composite c

-- "every link reflects", as a recursive predicate: `Unit*` at the empty
-- chain, so nothing is asserted about a chain of length zero.
Reflects : {T U : Theory ℓS ℓ ℓ' ℓX ℓP} → Chain T U
         → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))
Reflects done    = Unit*
Reflects (P ◅ c) = Reflective P × Reflects c

-- ==================================================================
-- THE THEOREM.  A chain of reflective passes is a reflective pass -- so
-- "keep enough data to project back to earlier passes" holds across the
-- WHOLE compiler, not one link at a time.
-- ==================================================================

chainReflective : {T U : Theory ℓS ℓ ℓ' ℓX ℓP} (c : Chain T U)
                → Reflects c → Reflective (composite c)
chainReflective {T = T} done  _       = idReflective T
chainReflective (P ◅ c)       (r , rs) = r ⨟R chainReflective c rs
