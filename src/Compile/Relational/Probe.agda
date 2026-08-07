{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module Compile.Relational.Probe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit

open import Compile.LinToRust.Codegen
import Compile.Semantics.CBV as S
import TheoryGrammar.Instances.LinLam.Syntax as L

tgt : Maybe RExpr
tgt = valOf (evalRust 20 (compileRust (L.tapp L.unil appLin L.idLin)))

src : RExpr
src = compileRust (S.evalV (L.tapp L.unil appLin L.idLin))

_ : tgt ≡ just (rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1))))
_ = refl

_ : src ≡ rClos 0 (rCall (rClos 1 (rVar (bnd 1))) (rVar (bnd 0)))
_ = refl
