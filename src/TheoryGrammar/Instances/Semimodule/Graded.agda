{- THE LAWS OF THE GRADED EXPONENTIAL, AND WHICH OF THEM ARE FREE. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Semimodule.Graded (Char : Type₀) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Equations
open import TheoryGrammar.Instances.Semimodule.Connectives Char public

-- The model, and the one-variable context.

M : Model semiSig ℓ-zero
M = ⌊ smPoint ⌋

V₁ : Type₀
V₁ = Unit

vs₁ : V₁ → MSort
vs₁ _ = elt

-- The flattened composites.  `Flat q A` is what `!⟨ q ⟩ A` looks like
-- after the `Equations` flattening; `Flat2 r s A` is the two-level
-- composite already collapsed; `Diag` is the NON-LINEAR shape.

Flat : ℕ → Elt → Elt
Flat q A = ⊗ᶠ M {V = V₁} {vs = vs₁} (λ ρ → rep q (ρ tt)) (λ _ → A)

Flat2 : ℕ → ℕ → Elt → Elt
Flat2 r s A = ⊗ᶠ M {V = V₁} {vs = vs₁} (λ ρ → rep r (rep s (ρ tt))) (λ _ → A)

FlatId : Elt → Elt
FlatId A = ⊗ᶠ M {V = V₁} {vs = vs₁} (λ ρ → ρ tt) (λ _ → A)

Diag : ℕ → ℕ → Elt → Elt
Diag r s A = ⊗ᶠ M {V = V₁} {vs = vs₁} (λ ρ → rep r (ρ tt) ++ rep s (ρ tt)) (λ _ → A)

-- congruence of the flattening in its payload
FlatCong : (q : ℕ) {A B : Elt} → ((x : String) → Iso (A x) (B x))
         → (m : String) → Iso (Flat q A m) (Flat q B m)
FlatCong q I m .Iso.fun (ρ , e , k) = ρ , e , λ v → I (ρ v) .Iso.fun (k v)
FlatCong q I m .Iso.inv (ρ , e , k) = ρ , e , λ v → I (ρ v) .Iso.inv (k v)
FlatCong q I m .Iso.sec (ρ , e , k) =
  ΣPathP (refl , ΣPathP (refl , funExt λ v → I (ρ v) .Iso.sec (k v)))
FlatCong q I m .Iso.ret (ρ , e , k) =
  ΣPathP (refl , ΣPathP (refl , funExt λ v → I (ρ v) .Iso.ret (k v)))

-- BRIDGE 1. One action tensor is its own flattening.

private
  repcong : {p q : ℕ} {w : String} → p Eq.≡ q → rep q w Eq.≡ rep p w
  repcong Eq.refl = Eq.refl

  repFwd : (q : ℕ) (A : Elt) (m : String) → Flat q A m → (!⟨ q ⟩ A) m
  repFwd q A _ (ρ , Eq.refl , k) = mkRep q (ρ tt) , pairB Eq.refl (k tt)

  repInv : (q : ℕ) (A : Elt) (m : String) → (!⟨ q ⟩ A) m → Flat q A m
  repInv q A _ (mkRep p w , h) = (λ _ → w) , repcong (h true) , (λ _ → h false)

  repSec : (q : ℕ) (A : Elt) (p : ℕ) (w : String) (e : p Eq.≡ q) (a : A w)
         → repFwd q A (rep p w) (repInv q A (rep p w) (mkRep p w , pairB e a))
           ≡ (mkRep p w , pairB e a)
  repSec q A _ w Eq.refl a = refl

repBridge : (q : ℕ) (A : Elt) (m : String) → Iso (Flat q A m) ((!⟨ q ⟩ A) m)
repBridge q A m .Iso.fun = repFwd q A m
repBridge q A m .Iso.inv = repInv q A m
repBridge q A m .Iso.sec (mkRep p w , h) =
    cong (λ k → repFwd q A (rep p w) (repInv q A (rep p w) (mkRep p w , k)))
         (sym (etaBool h))
  ∙ repSec q A p w (h true) (h false)
  ∙ ΣPathP (refl , etaBool h)
repBridge q A m .Iso.ret (ρ , Eq.refl , k) = refl

-- BRIDGE 2. THE FLATTENING ITSELF: a nested composite collapses.

private
  nestFwd : (r s : ℕ) (A : Elt) (m : String) → Flat r (Flat s A) m → Flat2 r s A m
  nestFwd r s A m (ρ , e , k) =
      k tt .fst
    , (Eq.ap (rep r) (k tt .snd .fst) Eq.∙ e)
    , k tt .snd .snd

  nestInv : (r s : ℕ) (A : Elt) (m : String) → Flat2 r s A m → Flat r (Flat s A) m
  nestInv r s A m (ρ , e , k) = (λ _ → rep s (ρ tt)) , e , (λ _ → ρ , Eq.refl , k)

  nestRet : (r s : ℕ) (A : Elt) (m : String) (w : String)
            (e : rep r w Eq.≡ m) (t : Flat s A w)
          → nestInv r s A m (nestFwd r s A m ((λ _ → w) , e , (λ _ → t)))
            ≡ ((λ _ → w) , e , (λ _ → t))
  nestRet r s A m _ e (ρ' , Eq.refl , k') = refl

flatNest : (r s : ℕ) (A : Elt) (m : String) → Iso (Flat r (Flat s A) m) (Flat2 r s A m)
flatNest r s A m .Iso.fun = nestFwd r s A m
flatNest r s A m .Iso.inv = nestInv r s A m
flatNest r s A m .Iso.sec _ = refl
flatNest r s A m .Iso.ret (ρ , e , k) = nestRet r s A m (ρ tt) e (k tt)

-- THE UNIT LAW, from `eqn→Iso` at a genuine equation of the theory.
-- act(one, x) = x One variable, used once: LINEAR.

unitLHS : Tm semiSig V₁ vs₁ elt
unitLHS = node actOp (pairB (node oneOp (λ ())) (var tt))

unitRHS : Tm semiSig V₁ vs₁ elt
unitRHS = var tt

-- the model satisfies it: rep 1 w ≡ w
unitSat : (ρ : Val M vs₁) → eval M ρ unitLHS Eq.≡ eval M ρ unitRHS
unitSat ρ = Eq.pathToEq (rep-one (ρ tt))

-- THE LIFTING THEOREM, applied.  Nothing about `!` appears here.
unitEqn : (A : Elt) (m : String) → Iso (FlatId A m) (Flat 1 A m)
unitEqn A m = eqn→Iso M unitLHS unitRHS {A = λ _ → A} unitSat m

-- the variable case of the bridge: a one-variable flattening at the
-- identity shape is a singleton contraction, definitional in Eq-world
idBridge : (A : Elt) (m : String) → Iso (FlatId A m) (A m)
idBridge A m .Iso.fun (ρ , Eq.refl , k) = k tt
idBridge A m .Iso.inv a = (λ _ → m) , Eq.refl , (λ _ → a)
idBridge A m .Iso.sec a = refl
idBridge A m .Iso.ret (ρ , Eq.refl , k) = refl

-- THE COUNIT OF THE GRADED COMONAD.
!-unit : (A : Elt) (m : String) → Iso ((!⟨ 1 ⟩ A) m) (A m)
!-unit A m =
  compIso (invIso (repBridge 1 A m))
    (compIso (invIso (unitEqn A m)) (idBridge A m))

-- and its `⊢` form, which is what a program uses
!-unit-E : (A : Elt) → (!⟨ 1 ⟩ A) ⊢ A
!-unit-E A m = !-unit A m .Iso.fun

!-unit-I : (A : Elt) → A ⊢ (!⟨ 1 ⟩ A)
!-unit-I A m = !-unit A m .Iso.inv

-- THE COMPOSITION LAW. (r·s)·w = r·(s·w) One variable, used once on each
-- side: LINEAR.

mulEqn : (r s : ℕ) (A : Elt) (m : String) → Iso (Flat (r · s) A m) (Flat2 r s A m)
mulEqn r s A m =
  ⊗ᶠ-cong M {V = V₁} {vs = vs₁}
    {f = λ ρ → rep (r · s) (ρ tt)}
    {g = λ ρ → rep r (rep s (ρ tt))}
    {A = λ _ → A}
    (λ ρ → Eq.sym (Eq.pathToEq (rep-mul r s (ρ tt))))
    m

-- THE COMULTIPLICATION OF THE GRADED COMONAD.
!-comp : (r s : ℕ) (A : Elt) (m : String)
       → Iso ((!⟨ r ⟩ (!⟨ s ⟩ A)) m) ((!⟨ r · s ⟩ A) m)
!-comp r s A m =
  compIso (invIso (repBridge r (!⟨ s ⟩ A) m))
    (compIso (invIso (FlatCong r (repBridge s A) m))
      (compIso (flatNest r s A m)
        (compIso (invIso (mulEqn r s A m)) (repBridge (r · s) A m))))

!-comp-E : (r s : ℕ) (A : Elt) → (!⟨ r ⟩ (!⟨ s ⟩ A)) ⊢ (!⟨ r · s ⟩ A)
!-comp-E r s A m = !-comp r s A m .Iso.fun

!-comp-I : (r s : ℕ) (A : Elt) → (!⟨ r · s ⟩ A) ⊢ (!⟨ r ⟩ (!⟨ s ⟩ A))
!-comp-I r s A m = !-comp r s A m .Iso.inv

-- THE NON-LINEAR LAW THAT IS TRUE. (r+s)·w = r·w ++ s·w One variable, used
-- ONCE on the left and TWICE on the right.

addEqn : (r s : ℕ) (A : Elt) (m : String) → Iso (Flat (r + s) A m) (Diag r s A m)
addEqn r s A m =
  ⊗ᶠ-cong M {V = V₁} {vs = vs₁}
    {f = λ ρ → rep (r + s) (ρ tt)}
    {g = λ ρ → rep r (ρ tt) ++ rep s (ρ tt)}
    {A = λ _ → A}
    (λ ρ → Eq.sym (Eq.pathToEq (rep-add r s (ρ tt))))
    m

-- PRIMITIVE (phase 1). THE COPY.
diag→⊗ : (r s : ℕ) (A : Elt) → Diag r s A ⊢ ((!⟨ r ⟩ A) ⊗ᵃ (!⟨ s ⟩ A))
diag→⊗ r s A _ (ρ , Eq.refl , k) =
  cat-I (splitAll (rep r (ρ tt)) (rep s (ρ tt)))
        (act-I r (ρ tt) Eq.refl (k tt))
        (act-I s (ρ tt) Eq.refl (k tt))

-- CONTRACTION for the graded exponential: free up to the copy.
!-contract : (r s : ℕ) (A : Elt) → (!⟨ r + s ⟩ A) ⊢ ((!⟨ r ⟩ A) ⊗ᵃ (!⟨ s ⟩ A))
!-contract r s A =
  diag→⊗ r s A
    ∘g (λ m → addEqn r s A m .Iso.fun)
    ∘g (λ m → repBridge (r + s) A m .Iso.inv)

-- The converse does NOT exist, and the reason is visible in the types:
-- `(!⟨r⟩A ⊗ᵃ !⟨s⟩A) m` supplies two independent witnesses `A u`, `A v`
-- with no reason for `u ≡ v`, while `!⟨r+s⟩A m` demands a single `w` with
-- `m = rep (r+s) w`.

-- THE NON-LINEAR LAW THAT IS FALSE. r·(u ++ v) = r·u ++ r·v Non-linear in
-- the GRADE: `r` occurs twice on the right.

-- THE GENERAL FORM: scalars as genuine variables.

data V₃ : Type₀ where
  xr xs xm : V₃

vs₃ : V₃ → MSort
vs₃ xr = scl
vs₃ xs = scl
vs₃ xm = elt

mulLHS : Tm semiSig V₃ vs₃ elt
mulLHS = node actOp (pairB (node mulOp (λ b → if b then var xr else var xs)) (var xm))

mulRHS : Tm semiSig V₃ vs₃ elt
mulRHS = node actOp (pairB (var xr) (node actOp (pairB (var xs) (var xm))))

-- the equation is satisfied in the model: rep (r · s) w ≡ rep r (rep s w)
mulSat : (ρ : Val M vs₃) → eval M ρ mulLHS Eq.≡ eval M ρ mulRHS
mulSat ρ = Eq.pathToEq (rep-mul (ρ xr) (ρ xs) (ρ xm))

-- so the lifting theorem fires, with no side condition:
mulEqn₃ : (Aᵥ : (v : V₃) → TheoryTy ℓ-zero (vs₃ v)) (m : String)
        → Iso (⟪_⟫ M mulRHS Aᵥ m) (⟪_⟫ M mulLHS Aᵥ m)
mulEqn₃ Aᵥ m = eqn→Iso M mulLHS mulRHS {A = Aᵥ} mulSat m

-- THE BRIDGE, AND THE ONE LEMMA IT NEEDS. `Val vs₃ = (v : V₃) → carrier
-- (vs₃ v)` has no η: a valuation reassembled slotwise as `λ { xr → … ; xs
-- → … ; xm → … }` is only PROPOSITIONALLY the valuation it came from, so a
-- naive bridge has an equation component sitting over a `funExt`, i.e. a
-- `PathP`...

-- the payload family, NAMED (an extended lambda would be a different
-- term in every file that wrote it out)
Aᵥ₃ : Scl → Scl → Elt → (v : V₃) → TheoryTy ℓ-zero (vs₃ v)
Aᵥ₃ R S A xr = R
Aᵥ₃ R S A xs = S
Aᵥ₃ R S A xm = A

Θ₃ : Scl → Scl → Elt → Type₀
Θ₃ R S A = (v : V₃) → Σ[ c ∈ MCarrier (vs₃ v) ] Aᵥ₃ R S A v c

-- the nested side:  Σ[θ] (rep (θxr) (rep (θxs) (θxm)) ≡ m)  ≅  ActG R (ActG S A)

private
  Nest₃ : (R S : Scl) (A : Elt) (m : String) → Type₀
  Nest₃ R S A m =
    Σ[ θ ∈ Θ₃ R S A ] (rep (θ xr .fst) (rep (θ xs .fst) (θ xm .fst)) Eq.≡ m)

  nest₃Fwd : (R S : Scl) (A : Elt) (m : String) → Nest₃ R S A m → ActG R (ActG S A) m
  nest₃Fwd R S A _ (θ , Eq.refl) =
      mkRep (θ xr .fst) (rep (θ xs .fst) (θ xm .fst))
    , pairB (θ xr .snd) (mkRep (θ xs .fst) (θ xm .fst) , pairB (θ xs .snd) (θ xm .snd))

  nest₃Inv : (R S : Scl) (A : Elt) (p : ℕ) (x : String)
           → R p → ActG S A x → Nest₃ R S A (rep p x)
  nest₃Inv R S A p _ y (mkRep q w , h) = θ₀ , Eq.refl
    where
      θ₀ : Θ₃ R S A
      θ₀ xr = p , y
      θ₀ xs = q , h true
      θ₀ xm = w , h false

  nest₃Sec : (R S : Scl) (A : Elt) (p : ℕ) (y : R p) (q : ℕ) (w : String)
             (z : S q) (a : A w)
           → nest₃Fwd R S A (rep p (rep q w))
               (nest₃Inv R S A p (rep q w) y (mkRep q w , pairB z a))
             ≡ (mkRep p (rep q w) , pairB y (mkRep q w , pairB z a))
  nest₃Sec R S A p y q w z a = refl

  nest₃Sec' : (R S : Scl) (A : Elt) (p : ℕ) (x : String) (y : R p) (t : ActG S A x)
            → nest₃Fwd R S A (rep p x) (nest₃Inv R S A p x y t)
              ≡ (mkRep p x , pairB y t)
  nest₃Sec' R S A p _ y (mkRep q w , h) =
      cong (λ k → nest₃Fwd R S A (rep p (rep q w))
                    (nest₃Inv R S A p (rep q w) y (mkRep q w , k)))
           (sym (etaBool h))
    ∙ nest₃Sec R S A p y q w (h true) (h false)
    ∙ (λ i → mkRep p (rep q w) , pairB y (mkRep q w , etaBool h i))

nest₃ : (R S : Scl) (A : Elt) (m : String)
      → Iso (Nest₃ R S A m) (ActG R (ActG S A) m)
nest₃ R S A m .Iso.fun = nest₃Fwd R S A m
nest₃ R S A m .Iso.inv (mkRep p x , h) = nest₃Inv R S A p x (h true) (h false)
nest₃ R S A m .Iso.sec (mkRep p x , h) =
  nest₃Sec' R S A p x (h true) (h false) ∙ (λ i → mkRep p x , etaBool h i)
-- HERE is where the missing η is paid, and where the reassociation earns
-- its keep: the funExt is over `Θ₃`, whose type does not mention the
-- valuation, so the equation component below is `refl` and not a `PathP`
-- over a `funExt`.
nest₃ R S A m .Iso.ret (θ , Eq.refl) =
  ΣPathP (funExt (λ { xr → refl ; xs → refl ; xm → refl }) , refl)

-- the multiplied side:  Σ[θ] (rep (θxr · θxs) (θxm) ≡ m)  ≅  ActG (R ·ᵍ S) A

private
  Mul₃ : (R S : Scl) (A : Elt) (m : String) → Type₀
  Mul₃ R S A m =
    Σ[ θ ∈ Θ₃ R S A ] (rep (θ xr .fst · θ xs .fst) (θ xm .fst) Eq.≡ m)

  mul₃Fwd : (R S : Scl) (A : Elt) (m : String) → Mul₃ R S A m → ActG (R ·ᵍ S) A m
  mul₃Fwd R S A _ (θ , Eq.refl) =
      mkRep (θ xr .fst · θ xs .fst) (θ xm .fst)
    , pairB (mkFac (θ xr .fst) (θ xs .fst) , pairB (θ xr .snd) (θ xs .snd)) (θ xm .snd)

  mul₃Inv : (R S : Scl) (A : Elt) (p : ℕ) (w : String)
          → (R ·ᵍ S) p → A w → Mul₃ R S A (rep p w)
  mul₃Inv R S A _ w (mkFac a b , h) a₀ = θ₀ , Eq.refl
    where
      θ₀ : Θ₃ R S A
      θ₀ xr = a , h true
      θ₀ xs = b , h false
      θ₀ xm = w , a₀

  mul₃Sec : (R S : Scl) (A : Elt) (a b : ℕ) (w : String)
            (x : R a) (y : S b) (a₀ : A w)
          → mul₃Fwd R S A (rep (a · b) w)
              (mul₃Inv R S A (a · b) w (mkFac a b , pairB x y) a₀)
            ≡ (mkRep (a · b) w , pairB (mkFac a b , pairB x y) a₀)
  mul₃Sec R S A a b w x y a₀ = refl

  mul₃Sec' : (R S : Scl) (A : Elt) (p : ℕ) (w : String)
             (t : (R ·ᵍ S) p) (a₀ : A w)
           → mul₃Fwd R S A (rep p w) (mul₃Inv R S A p w t a₀)
             ≡ (mkRep p w , pairB t a₀)
  mul₃Sec' R S A _ w (mkFac a b , h) a₀ =
      cong (λ k → mul₃Fwd R S A (rep (a · b) w)
                    (mul₃Inv R S A (a · b) w (mkFac a b , k) a₀))
           (sym (etaBool h))
    ∙ mul₃Sec R S A a b w (h true) (h false) a₀
    ∙ (λ i → mkRep (a · b) w , pairB (mkFac a b , etaBool h i) a₀)

mul₃ : (R S : Scl) (A : Elt) (m : String)
     → Iso (Mul₃ R S A m) (ActG (R ·ᵍ S) A m)
mul₃ R S A m .Iso.fun = mul₃Fwd R S A m
mul₃ R S A m .Iso.inv (mkRep p w , h) = mul₃Inv R S A p w (h true) (h false)
mul₃ R S A m .Iso.sec (mkRep p w , h) =
  mul₃Sec' R S A p w (h true) (h false) ∙ (λ i → mkRep p w , etaBool h i)
mul₃ R S A m .Iso.ret (θ , Eq.refl) =
  ΣPathP (funExt (λ { xr → refl ; xs → refl ; xm → refl }) , refl)

-- THE BRIDGES, and THE GENERAL COMPOSITION LAW.

flat3Bridge : (R S : Scl) (A : Elt) (m : String)
            → Iso (⟪_⟫ M mulRHS (Aᵥ₃ R S A) m) (ActG R (ActG S A) m)
flat3Bridge R S A m =
  compIso (⊗ᶠ-reassoc M (λ ρ → eval M ρ mulRHS) (Aᵥ₃ R S A) m) (nest₃ R S A m)

flat3Bridge' : (R S : Scl) (A : Elt) (m : String)
             → Iso (⟪_⟫ M mulLHS (Aᵥ₃ R S A) m) (ActG (R ·ᵍ S) A m)
flat3Bridge' R S A m =
  compIso (⊗ᶠ-reassoc M (λ ρ → eval M ρ mulLHS) (Aᵥ₃ R S A) m) (mul₃ R S A m)

-- THE COMULTIPLICATION, at ARBITRARY scalar grammars, straight from
-- `eqn→Iso`.  `!-comp` above is this at `R = ⌈ r ⌉`, `S = ⌈ s ⌉`.
·ᵍ-comp : (R S : Scl) (A : Elt) (m : String)
        → Iso (ActG R (ActG S A) m) (ActG (R ·ᵍ S) A m)
·ᵍ-comp R S A m =
  compIso (invIso (flat3Bridge R S A m))
    (compIso (mulEqn₃ (Aᵥ₃ R S A) m) (flat3Bridge' R S A m))

-- PRIMITIVES (phase 1): the same two maps, written by hand, for comparison
-- with what `eqn→Iso` produced above.
private
  actMulGo : {R S : Scl} {A : Elt} (p : ℕ) (w : String)
           → (R ·ᵍ S) p → A w → ActG R (ActG S A) (rep p w)
  actMulGo {R} {S} {A} _ w (mkFac a b , h) a₀ =
    subst (ActG R (ActG S A)) (sym (rep-mul a b w))
      (act-I a (rep b w) (h true) (act-I b w (h false) a₀))

  mulActGo : {R S : Scl} {A : Elt} (p : ℕ) (x : String)
           → R p → ActG S A x → ActG (R ·ᵍ S) A (rep p x)
  mulActGo {R} {S} {A} p _ y (mkRep q w , h) =
    subst (ActG (R ·ᵍ S) A) (rep-mul p q w)
      (act-I (p · q) w (mul-I p q y (h true)) (h false))

·ᵍ-act : {R S : Scl} {A : Elt} → ActG (R ·ᵍ S) A ⊢ ActG R (ActG S A)
·ᵍ-act _ (mkRep p w , h) = actMulGo p w (h true) (h false)

act-·ᵍ : {R S : Scl} {A : Elt} → ActG R (ActG S A) ⊢ ActG (R ·ᵍ S) A
act-·ᵍ _ (mkRep p x , h) = mulActGo p x (h true) (h false)

-- Specialising the general form at representables recovers the numeral
-- law, using that ⌈r⌉ ·ᵍ ⌈s⌉ IS ⌈r · s⌉ (`Connectives.agda`).
!-comp-E' : (r s : ℕ) (A : Elt) → (!⟨ r ⟩ (!⟨ s ⟩ A)) ⊢ (!⟨ r · s ⟩ A)
!-comp-E' r s A =
  (λ m → ActG-congˡ A (⌈⌉·⌈⌉≅⌈·⌉ r s) m .Iso.fun) ∘g act-·ᵍ
