{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PASS 2.  THE LINEARITY CHECKER, AS AN INTERNAL DECISION.

  The statement to be proved is

      linear? : ⊤G ⊢ Dec⟨ Lin ⟩          over `dbFib`

  -- a map out of the terminal grammar into a sum, together with the
  exclusion that `Dec⟨_⟩` carries by construction (`¬G-excludes`, hence
  `linDecision` below).  There is no metalanguage `Dec` in the
  interface and no `Bool`: `linearB` exists, but it is the GENERIC `okA`
  applied afterwards, exactly as `TheoryGrammar.SemanticAction`
  prescribes -- externalise late.

  --------------------------------------------------------------------
  WHAT `Lin` SAYS, and why it is the right grammar.

      Lin m  =  Σ[ u ∈ Usage ]  length u ≡ fst m
                             ×  Σ[ e ∈ Tm u ] (eraseS e ≡ skel (snd m))

  "`m` is, up to scope bookkeeping, the erasure of a linear term."  `Tm`
  is `LinLam/Syntax`'s linear syntax over the CONTEXT PROMODEL, so a
  `Tm u` is linearity-correct by construction: `tapp` CARRIES a `Use⊎`,
  and the absent `(true,true)` constructor is the whole of the
  no-duplication condition.  Hence the checker never compares multisets
  of variables -- producing a `Tm u` IS the certificate.  The usage `u`
  is existential, so a free variable the term does not mention is simply
  `false` in `u`; a BOUND variable cannot be, because `tlam` consumes a
  `Tm (true ∷ u)` and the `true` has to be spent.

  --------------------------------------------------------------------
  WHY THERE IS A `Skel` TYPE, i.e. why the erasure equation is stated on
  an UNSCOPED shadow.  This is the one design decision in the file and
  it is forced.

  The obvious statement is `eraseΣ e Eq.≡ m` in `Term• = Σ[n] DBTm n`.
  It does not work.  A linear term at usage `u` erases at scope
  `length u`, and `Use⊎ u₁ u₂ w` makes the three lengths equal only
  PROPOSITIONALLY, so `erase` at an application must coerce its two
  subtrees into the whole's scope.  Combining two such equations then
  needs `(m , x) ≡ (n , U)` and `(m , y) ≡ (n , V)` to give
  `(m , dapp x y) ≡ (n , dapp U V)` -- and that is not provable by
  matching, because after the first `Eq.refl` the second forces
  eliminating the reflexive equation `m = m`, which is exactly K.  (Agda
  says so: `Cannot eliminate reflexive equation m = m ... because K has
  been disabled`.)  One could route around it through `isSet ℕ`; it is
  simpler and more honest to remove the index.

  So the erasure lands in `Skel`, de Bruijn syntax with the scope
  forgotten, and the scope constraint becomes a SEPARATE, purely
  propositional component `length u Eq.≡ n` that is never transported
  along.  Every equation in the file is then between two constructor
  applications of a NON-INDEXED datatype, every inversion is one
  `Eq.refl` match, and no coercion appears anywhere.

  That is a real lesson about the scoped carrier chosen in `DB.agda`:
  putting the scope in the index makes `Scoped` trivial (which is what
  it was for) and makes EQUATIONS BETWEEN TERMS awkward, because the
  index has to be carried.  Splitting the two -- structure in the index,
  equality on the skeleton -- costs one 3-constructor datatype.

  --------------------------------------------------------------------
  THE ARCHITECTURE: ONE COALGEBRA, TWO ALGEBRAS.

  This is `Instances/Bags/Quicksort` transplanted.  There, `bagCase` is a
  coalgebra out of `⊤` and the SAME coalgebra is run at two algebras --
  one producing the sorted bag, one producing the bag WITH its
  permutation proof.  Here the coalgebra is `DB.dbCase`, the
  decomposition axiom of the de Bruijn theory, and it is not written in
  this file at all; the algebras are `linAlg` (the decision, carrying its
  own certificate) and `sizeAlg` (a plain semantic action), and the
  recursion in both cases is `runAut` -- i.e. `hyloC`, i.e. `löb` -- with
  `dbGuarded` as the termination certificate.  No recursion is written
  here, and no de Bruijn constructor is matched here.

  What the algebra does at each node is the typing rule read backwards:

      dvar i     always linear, at the usage `only i`
      dapp U V   both children linear AND their usages JOIN
      dlam b     the child linear AND its usage has `true` at the head

  and at `dapp`, "their usages join" is `Join u₁ u₂ = Σ[w] Use⊎ u₁ u₂ w`
  -- EXHIBITING a splitting of the linear promodel.  That is the design
  claim of `LinLam/Context`: linear application is `⊗ˢ appop`, so the
  side condition of the rule IS the splitting relation and there is
  nothing else to check.  `linApp` is the proof: it inspects neither
  `e₁` nor `e₂`, it receives a `Use⊎` and applies `tapp`.

  --------------------------------------------------------------------
  WHERE THE FRAMEWORK DOES NOT REACH.  Two places, both reported because
  they are more useful than the positive story.

  (1) `join?` is a metalanguage `⊎`, not an internal `Dec⟨_⟩`, and it has
  to be.  `Use⊎` is a splitting of `linFib`, which lives over
  `monoidSig`, while everything else here lives over `λSig`.
  `CarrierMap.Reindex` relates two promodels over ONE signature, so there
  is NO `Reindex` between the de Bruijn theory and the linear-context
  theory, and the bridge cannot be a map of promodels at all.

      BELONGS UPSTREAM: `Reindex` along a MAP OF SIGNATURES -- a functor
      on operations/arities together with a carrier map over the induced
      sort map.  With it, `join?` would be the image of the linear
      theory's own decision for `Split appop` (`Decidable.Splittings`),
      and this file would contain no `⊎` at all.  Without it the two
      theories can only meet in the metalanguage.  The same fact is why
      `Syntax` is imported `using` only its DATA below: opening its
      connectives would shadow every name of `dbFib`'s calculus, and the
      shadowing is not a naming accident.

  (2) `linUniq` -- "the usage of a linear term is determined by its
  skeleton and scope" -- is what every REFUTATION branch needs, and it
  is a fact about `eraseS`, not about the calculus.  It is proved here,
  in full, by ordinary induction on two linear terms; the framework
  shortened none of it.  That asymmetry is the honest measure of what
  working internally bought: the POSITIVE rules are free (`linApp`
  checks nothing -- it receives a splitting and applies `tapp`), the
  NEGATIVE ones are ordinary syntax.  See the note at its definition.

  --------------------------------------------------------------------
  PRIMITIVE (phase 1): `Skel`, `skel`, `soloIxℕ`, `eraseS`, `u⊎L`/`u⊎R`,
  the three injectivities, `onlyF`/`onlySolo`/`onlyIxℕ`/`lenOnly`,
  `linVar`, `linApp`/`linApp⁻`, `linLam⁻`/`reLam`, `lamDec`,
  `noApp`/`noLam`, `join?`.  Everything from `varCase` down is
  composition.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Check where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.FinData.Base using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

-- The DE BRUIJN theory, whose calculus this file is written in.
open import TheoryGrammar.Instances.LinLam.DB

-- The LINEAR theory, taken as DATA ONLY.  Its connectives are NOT
-- opened: they live over `monoidSig` and would shadow every name of the
-- calculus above.  See (1) in the header -- that shadowing is the same
-- fact as the missing `Reindex`.
open import TheoryGrammar.Instances.LinLam.Syntax
  using (Tm; tvar; tapp; tlam; Solo; Usage; Use⊎;
         unil; uleft; uright; uskip; Empty; none)

-- ==================================================================
-- THE SKELETON: de Bruijn syntax with the scope forgotten.  Both the
-- carrier and the linear syntax map into it, and EVERY equation in this
-- file is an equation of skeletons.  See the header for why.
-- ==================================================================

data Skel : Type₀ where                          -- PRIMITIVE
  svar : ℕ → Skel
  sapp : Skel → Skel → Skel
  slam : Skel → Skel

skel : {n : ℕ} → DBTm n → Skel                   -- PRIMITIVE
skel (dvar i)   = svar (toℕ i)
skel (dapp u v) = sapp (skel u) (skel v)
skel (dlam b)   = slam (skel b)

-- Unique readability of `Skel`, as three one-line inversions.  These
-- are the entire reason the file has no coercions: `Skel` is not
-- indexed, so `Eq.refl` matches without eliminating any equation
-- between indices.
sappInj₁ : {x y X Y : Skel} → sapp x y Eq.≡ sapp X Y → x Eq.≡ X
sappInj₁ Eq.refl = Eq.refl

sappInj₂ : {x y X Y : Skel} → sapp x y Eq.≡ sapp X Y → y Eq.≡ Y
sappInj₂ Eq.refl = Eq.refl

slamInj : {x X : Skel} → slam x Eq.≡ slam X → x Eq.≡ X
slamInj Eq.refl = Eq.refl

sappCong : {x y X Y : Skel} → x Eq.≡ X → y Eq.≡ Y → sapp x y Eq.≡ sapp X Y
sappCong Eq.refl Eq.refl = Eq.refl

-- ==================================================================
-- ERASURE: linear syntax → skeleton.  No coercion, no index.
-- ==================================================================

-- PRIMITIVE (phase 1): reading the index of the unique live variable.
soloIxℕ : (u : Usage) → Solo u → ℕ
soloIxℕ []          ()
soloIxℕ (true  ∷ u) e = 0
soloIxℕ (false ∷ u) s = suc (soloIxℕ u s)

-- PRIMITIVE (phase 1)
eraseS : {u : Usage} → Tm u → Skel
eraseS (tvar {u} s)   = svar (soloIxℕ u s)
eraseS (tapp s e₁ e₂) = sapp (eraseS e₁) (eraseS e₂)
eraseS (tlam e)       = slam (eraseS e)

-- the lengths a splitting equates -- used only for the SCOPE component
-- of `Lin`, never inside an erasure
u⊎L : {u₁ u₂ w : Usage} → Use⊎ u₁ u₂ w → length u₁ Eq.≡ length w
u⊎L unil       = Eq.refl
u⊎L (uleft s)  = Eq.ap suc (u⊎L s)
u⊎L (uright s) = Eq.ap suc (u⊎L s)
u⊎L (uskip s)  = Eq.ap suc (u⊎L s)

u⊎R : {u₁ u₂ w : Usage} → Use⊎ u₁ u₂ w → length u₂ Eq.≡ length w
u⊎R unil       = Eq.refl
u⊎R (uleft s)  = Eq.ap suc (u⊎R s)
u⊎R (uright s) = Eq.ap suc (u⊎R s)
u⊎R (uskip s)  = Eq.ap suc (u⊎R s)

predEq : {m n : ℕ} → suc m Eq.≡ suc n → m Eq.≡ n
predEq Eq.refl = Eq.refl

-- ==================================================================
-- THE GRAMMAR BEING DECIDED.
-- ==================================================================

Lin : TmG
Lin m = Σ[ u ∈ Usage ] ((length u Eq.≡ m .fst)
                        × (Σ[ e ∈ Tm u ] (eraseS e Eq.≡ skel (m .snd))))

-- ==================================================================
-- THE VARIABLE RULE.  A de Bruijn variable is linear at the usage that
-- owns exactly it; the content is that `only` reads back, which is now
-- a plain equation of NATURAL NUMBERS.
-- ==================================================================

onlyF : {n : ℕ} → Fin n → Usage                  -- PRIMITIVE
onlyF {suc n} fzero    = true ∷ none n
onlyF         (fsuc i) = false ∷ onlyF i

emptyNone : (n : ℕ) → Empty (none n)
emptyNone zero    = tt
emptyNone (suc n) = emptyNone n

onlySolo : {n : ℕ} (i : Fin n) → Solo (onlyF i)
onlySolo {suc n} fzero    = emptyNone n
onlySolo         (fsuc i) = onlySolo i

noneLen : (n : ℕ) → length (none n) Eq.≡ n
noneLen zero    = Eq.refl
noneLen (suc n) = Eq.ap suc (noneLen n)

lenOnly : {n : ℕ} (i : Fin n) → length (onlyF i) Eq.≡ n
lenOnly {suc n} fzero    = Eq.ap suc (noneLen n)
lenOnly         (fsuc i) = Eq.ap suc (lenOnly i)

-- `only` reads back
onlyIxℕ : {n : ℕ} (i : Fin n) → soloIxℕ (onlyF i) (onlySolo i) Eq.≡ toℕ i
onlyIxℕ {suc n} fzero    = Eq.refl
onlyIxℕ         (fsuc i) = Eq.ap suc (onlyIxℕ i)

-- PRIMITIVE (phase 1)
linVar : (n : ℕ) (i : Fin n) → Lin (n , dvar i)
linVar n i =
  onlyF i , lenOnly i , tvar (onlySolo i) , Eq.ap svar (onlyIxℕ i)

-- ==================================================================
-- JOINING TWO USAGES.  See (1) in the header: this is the one place
-- where the two theories meet, and it is in the metalanguage because
-- `Reindex` cannot cross a change of signature.
--
-- Read the clauses.  The only negative case that is not a shape
-- mismatch is `(true ∷ u) (true ∷ v)` -- both premises claim the same
-- variable -- and it is refuted by the ABSENT constructor of `Use⊎`,
-- never by counting.
-- ==================================================================

Join : Usage → Usage → Type₀
Join u v = Σ[ w ∈ Usage ] Use⊎ u v w

Dec⊎ : Type₀ → Type₀
Dec⊎ A = A ⊎ (A → ⊥)

private
  invL : {u v w : Usage} → Use⊎ (true ∷ u) (false ∷ v) w → Join u v
  invL (uleft s) = _ , s

  invR : {u v w : Usage} → Use⊎ (false ∷ u) (true ∷ v) w → Join u v
  invR (uright s) = _ , s

  invS : {u v w : Usage} → Use⊎ (false ∷ u) (false ∷ v) w → Join u v
  invS (uskip s) = _ , s

  nilCons : {b : Bool} {v : Usage} → Join [] (b ∷ v) → ⊥
  nilCons (w , ())

  consNil : {b : Bool} {u : Usage} → Join (b ∷ u) [] → ⊥
  consNil (w , ())

  -- THE MISSING CONSTRUCTOR, used.
  dupUse : {u v : Usage} → Join (true ∷ u) (true ∷ v) → ⊥
  dupUse (w , ())

  goL : (u v : Usage) → Dec⊎ (Join u v) → Dec⊎ (Join (true ∷ u) (false ∷ v))
  goL u v (inl (w , s)) = inl (true ∷ w , uleft s)
  goL u v (inr k)       = inr (λ j → k (invL (j .snd)))

  goR : (u v : Usage) → Dec⊎ (Join u v) → Dec⊎ (Join (false ∷ u) (true ∷ v))
  goR u v (inl (w , s)) = inl (true ∷ w , uright s)
  goR u v (inr k)       = inr (λ j → k (invR (j .snd)))

  goS : (u v : Usage) → Dec⊎ (Join u v) → Dec⊎ (Join (false ∷ u) (false ∷ v))
  goS u v (inl (w , s)) = inl (false ∷ w , uskip s)
  goS u v (inr k)       = inr (λ j → k (invS (j .snd)))

-- PRIMITIVE (phase 1)
join? : (u v : Usage) → Dec⊎ (Join u v)
join? []          []          = inl ([] , unil)
join? []          (b ∷ v)     = inr nilCons
join? (b ∷ u)     []          = inr consNil
join? (true  ∷ u) (true  ∷ v) = inr dupUse
join? (true  ∷ u) (false ∷ v) = goL u v (join? u v)
join? (false ∷ u) (true  ∷ v) = goR u v (join? u v)
join? (false ∷ u) (false ∷ v) = goS u v (join? u v)

joinCoe : {a a' b b' : Usage} → a Eq.≡ a' → b Eq.≡ b' → Join a b → Join a' b'
joinCoe Eq.refl Eq.refl j = j

-- ==================================================================
-- THE APPLICATION RULE, and its inversion.  Note what `linApp` does
-- NOT do: it inspects neither subterm.  It receives a `Use⊎` and
-- applies `tapp`.
-- ==================================================================

-- PRIMITIVE (phase 1)
linApp : {n : ℕ} {U V : DBTm n} (l₁ : Lin (n , U)) (l₂ : Lin (n , V))
       → Join (l₁ .fst) (l₂ .fst) → Lin (n , dapp U V)
linApp (u₁ , p₁ , e₁ , q₁) (u₂ , p₂ , e₂ , q₂) (w , s) =
  w , (Eq.sym (u⊎L s) Eq.∙ p₁) , tapp s e₁ e₂ , sappCong q₁ q₂

-- PRIMITIVE (phase 1): unique readability of `eraseS` at an application.
linApp⁻ : {n : ℕ} {U V : DBTm n} → Lin (n , dapp U V)
        → Σ[ l₁ ∈ Lin (n , U) ] Σ[ l₂ ∈ Lin (n , V) ]
            Join (l₁ .fst) (l₂ .fst)
linApp⁻ (w , pw , tvar s , ())
linApp⁻ (w , pw , tlam e , ())
linApp⁻ (w , pw , tapp {u₁} {u₂} s e₁ e₂ , p) =
    (u₁ , (u⊎L s Eq.∙ pw) , e₁ , sappInj₁ p)
  , (u₂ , (u⊎R s Eq.∙ pw) , e₂ , sappInj₂ p)
  , (w , s)

-- PRIMITIVE (phase 1): ... and at an abstraction.  The codomain records
-- that the body's usage begins with `true`: the bound variable IS used,
-- which is the difference between linear and affine.
LamData : (n : ℕ) → DBTm (suc n) → Type₀
LamData n b = Σ[ u ∈ Usage ] ((length u Eq.≡ n)
                × (Σ[ e ∈ Tm (true ∷ u) ] (eraseS e Eq.≡ skel b)))

linLam⁻ : {n : ℕ} {b : DBTm (suc n)} → Lin (n , dlam b) → LamData n b
linLam⁻ (w , pw , tvar s       , ())
linLam⁻ (w , pw , tapp s e₁ e₂ , ())
linLam⁻ (w , pw , tlam e       , p) = w , pw , e , slamInj p

reLam : {n : ℕ} {b : DBTm (suc n)} → LamData n b → Lin (suc n , b)
reLam (u , pw , e , p) = (true ∷ u) , Eq.ap suc pw , e , p

-- ==================================================================
-- THE ONE FACT THE CALCULUS GIVES NO HELP WITH.
--
-- Every POSITIVE branch is discharged by the syntax: to say "this term
-- is linear" you exhibit a `Tm u`.  Every NEGATIVE branch needs
-- something the syntax does not give -- that the witness the recursive
-- call found is the ONLY one.  Concretely, at `dapp U V` the checker
-- learns that `U` is linear at `u₁`, that `V` is linear at `u₂`, and
-- that `u₁`, `u₂` do not join; to conclude that `dapp U V` is not
-- linear it must know that no OTHER pair of usages would have worked.
--
-- That is `linUniq`: the usage of a linear term is determined by its
-- skeleton and its scope.  It is a fact about `eraseS`, proved below by
-- induction on TWO linear terms with a common skeleton -- nine cases,
-- five of them constructor clashes -- plus three substrate lemmas
-- (`emptyUniq`, `soloUniq`, `joinFun`) that are facts about `Usage` and
-- `Use⊎`, i.e. about the LINEAR promodel and not about this one.
--
-- Recorded plainly: this is the part of the development the framework
-- did not shorten.  The internal layer discharged the positive rules
-- (see `linApp`, which checks nothing); the refutations are exactly the
-- residue, and they are ordinary syntactic induction.
-- ==================================================================

private
  svarInj : {a b : ℕ} → svar a Eq.≡ svar b → a Eq.≡ b
  svarInj Eq.refl = Eq.refl

  consEq : {b c : Bool} {u v : Usage} → (b ∷ u) Eq.≡ (c ∷ v) → u Eq.≡ v
  consEq Eq.refl = Eq.refl

  -- a usage that owns nothing is determined by its length
  emptyUniq : {u v : Usage} → Empty u → Empty v
            → length u Eq.≡ length v → u Eq.≡ v
  emptyUniq {[]}        {[]}        eu ev p  = Eq.refl
  emptyUniq {[]}        {_ ∷ _}     eu ev ()
  emptyUniq {_ ∷ _}     {[]}        eu ev ()
  emptyUniq {true  ∷ u} {_ ∷ _}     eu ev p  = E.rec eu
  emptyUniq {false ∷ u} {true  ∷ v} eu ev p  = E.rec ev
  emptyUniq {false ∷ u} {false ∷ v} eu ev p  =
    Eq.ap (false ∷_) (emptyUniq eu ev (predEq p))

  -- ... and one that owns exactly one variable is determined by its
  -- length together with WHICH variable
  soloUniq : {u v : Usage} (s : Solo u) (s' : Solo v)
           → length u Eq.≡ length v
           → soloIxℕ u s Eq.≡ soloIxℕ v s' → u Eq.≡ v
  soloUniq {[]}                        s s' p q  = E.rec s
  soloUniq {_ ∷ _}     {[]}            s s' p q  = E.rec s'
  soloUniq {true  ∷ u} {true  ∷ v}     s s' p q  =
    Eq.ap (true ∷_) (emptyUniq s s' (predEq p))
  soloUniq {true  ∷ u} {false ∷ v}     s s' p ()
  soloUniq {false ∷ u} {true  ∷ v}     s s' p ()
  soloUniq {false ∷ u} {false ∷ v}     s s' p q  =
    Eq.ap (false ∷_) (soloUniq s s' (predEq p) (predEq q))

  -- THE JOIN IS A FUNCTION.  `Use⊎` is a relation, but it is
  -- single-valued in its output -- which is exactly why "the context
  -- splits" is a side condition with no choice in it.
  joinFun : {u₁ u₂ w w' : Usage} → Use⊎ u₁ u₂ w → Use⊎ u₁ u₂ w' → w Eq.≡ w'
  joinFun unil       unil        = Eq.refl
  joinFun (uleft s)  (uleft s')  = Eq.ap (true  ∷_) (joinFun s s')
  joinFun (uright s) (uright s') = Eq.ap (true  ∷_) (joinFun s s')
  joinFun (uskip s)  (uskip s')  = Eq.ap (false ∷_) (joinFun s s')

  useCoe : {u₁ u₂ v₁ v₂ w : Usage} → u₁ Eq.≡ v₁ → u₂ Eq.≡ v₂
         → Use⊎ v₁ v₂ w → Use⊎ u₁ u₂ w
  useCoe Eq.refl Eq.refl s = s

  usageUniq : {u v : Usage} (e : Tm u) (f : Tm v)
            → length u Eq.≡ length v → eraseS e Eq.≡ eraseS f → u Eq.≡ v
  usageUniq (tvar {u} s)     (tvar {v} s')       pl q  =
    soloUniq s s' pl (svarInj q)
  usageUniq (tvar s)         (tapp s' f₁ f₂)     pl ()
  usageUniq (tvar s)         (tlam f)            pl ()
  usageUniq (tapp s e₁ e₂)   (tvar s')           pl ()
  usageUniq (tapp s e₁ e₂)   (tlam f)            pl ()
  usageUniq (tlam e)         (tvar s')           pl ()
  usageUniq (tlam e)         (tapp s' f₁ f₂)     pl ()
  usageUniq (tlam e)         (tlam f)            pl q  =
    consEq (usageUniq e f (Eq.ap suc pl) (slamInj q))
  usageUniq (tapp {u₁} {u₂} s e₁ e₂) (tapp {v₁} {v₂} s' f₁ f₂) pl q =
    joinFun s (useCoe h₁ h₂ s')
    where
    h₁ : u₁ Eq.≡ v₁
    h₁ = usageUniq e₁ f₁ (u⊎L s Eq.∙ (pl Eq.∙ Eq.sym (u⊎L s')))
                   (sappInj₁ q)

    h₂ : u₂ Eq.≡ v₂
    h₂ = usageUniq e₂ f₂ (u⊎R s Eq.∙ (pl Eq.∙ Eq.sym (u⊎R s')))
                   (sappInj₂ q)

linUniq : (m : Term•) (a b : Lin m) → a .fst Eq.≡ b .fst
linUniq m (u , pu , e , qe) (v , pv , f , qf) =
  usageUniq e f (pu Eq.∙ Eq.sym pv) (qe Eq.∙ Eq.sym qf)

private
  trueNotFalse : {a b : Usage} → (true ∷ a) Eq.≡ (false ∷ b) → ⊥
  trueNotFalse ()

noApp : {n : ℕ} {U V : DBTm n} (l₁ : Lin (n , U)) (l₂ : Lin (n , V))
      → (Join (l₁ .fst) (l₂ .fst) → ⊥) → Lin (n , dapp U V) → ⊥
noApp {n} {U} {V} l₁ l₂ k l =
  k (joinCoe (linUniq (n , U) (linApp⁻ l .fst) l₁)
             (linUniq (n , V) (linApp⁻ l .snd .fst) l₂)
             (linApp⁻ l .snd .snd))

noLam : {n : ℕ} {b : DBTm (suc n)} {u : Usage}
        (pw : length (false ∷ u) Eq.≡ suc n)
        (e : Tm (false ∷ u)) (p : eraseS e Eq.≡ skel b)
      → Lin (n , dlam b) → ⊥
noLam {n} {b} {u} pw e p l =
  trueNotFalse (linUniq (suc n , b) (reLam (linLam⁻ l))
                        ((false ∷ u) , pw , e , p))

-- ==================================================================
-- THE ALGEBRA.  Three cases, one per operation, each an elimination
-- rule of `DB.agda` followed by `dec-elim`.  No `with`, no `yes`/`no`
-- pattern, no metalanguage `Dec` in any type.
-- ==================================================================

varCase : VarG ⊤G ⊢ Dec⟨ Lin ⟩
varCase = dvar-elim λ n i _ → dec-yes Lin (n , dvar i) (linVar n i)

private
  appBoth : (n : ℕ) (U V : DBTm n) (l₁ : Lin (n , U)) (l₂ : Lin (n , V))
          → Dec⊎ (Join (l₁ .fst) (l₂ .fst)) → Dec⟨ Lin ⟩ (n , dapp U V)
  appBoth n U V l₁ l₂ (inl j) =
    dec-yes Lin (n , dapp U V) (linApp l₁ l₂ j)
  appBoth n U V l₁ l₂ (inr k) =
    dec-no Lin (n , dapp U V) (λ l → E.rec (noApp l₁ l₂ k l))

  appStep : (n : ℕ) (U V : DBTm n)
          → Dec⟨ Lin ⟩ (n , U) → Dec⟨ Lin ⟩ (n , V)
          → Dec⟨ Lin ⟩ (n , dapp U V)
  appStep n U V d₁ d₂ =
    dec-elim Lin (n , U)
      (λ l₁ → dec-elim Lin (n , V)
                (λ l₂ → appBoth n U V l₁ l₂ (join? (l₁ .fst) (l₂ .fst)))
                (λ k → dec-no Lin (n , dapp U V)
                         (λ l → k (linApp⁻ l .snd .fst)))
                d₂)
      (λ k → dec-no Lin (n , dapp U V) (λ l → k (linApp⁻ l .fst)))
      d₁

appCase : AppG Dec⟨ Lin ⟩ Dec⟨ Lin ⟩ ⊢ Dec⟨ Lin ⟩
appCase = dapp-elim appStep

private
  -- The binder's own condition: the body must USE the variable the
  -- binder introduced, i.e. its usage must begin with `true`.  A `false`
  -- head is AFFINE, not linear, and is refuted.
  lamDec : {n : ℕ} {b : DBTm (suc n)} → Lin (suc n , b)
         → Dec⟨ Lin ⟩ (n , dlam b)
  lamDec         ([]        , ()  , e , p)
  lamDec {n} {b} (true  ∷ u , pw , e , p) =
    dec-yes Lin (n , dlam b) (u , predEq pw , tlam e , Eq.ap slam p)
  lamDec {n} {b} (false ∷ u , pw , e , p) =
    dec-no Lin (n , dlam b) (λ l → E.rec (noLam pw e p l))

  lamStep : (n : ℕ) (b : DBTm (suc n)) → ⊤G {s = nm} (suc n , fzero)
          → Dec⟨ Lin ⟩ (suc n , b) → Dec⟨ Lin ⟩ (n , dlam b)
  lamStep n b _ d =
    dec-elim Lin (suc n , b)
      lamDec
      (λ k → dec-no Lin (n , dlam b) (λ l → k (reLam (linLam⁻ l))))
      d

lamCase : LamG ⊤G Dec⟨ Lin ⟩ ⊢ Dec⟨ Lin ⟩
lamCase = dlam-elim lamStep

-- ==================================================================
-- ... AND THE PROGRAM.  From here down nothing is written but
-- composition: the step is `⊕-E` of the three cases, the algebra is the
-- step after the container/connective respelling, and the recursion is
-- `runAut` -- the generic "⊤ carries a coalgebra AND the description is
-- guarded ⟹ run it" of `TheoryGrammar.Automaton`.
-- ==================================================================

LinFam : Fam
LinFam _ = Dec⟨ Lin ⟩

linStep : DBStep Dec⟨ Lin ⟩ ⊢ Dec⟨ Lin ⟩
linStep = ⊕-E varCase (⊕-E appCase lamCase)

linAlg : Algᴳ DBF LinFam
linAlg tt = linStep ∘g ⟦DB⟧ {M = ⌞ LinFam ⌟}

-- THE DECISION, INTERNALLY.
linear? : ⊤G ⊢ Dec⟨ Lin ⟩
linear? = runAut (guarded→LC dbGuarded) dbCase linAlg tt

-- ... and it IS a decision in the sense of `Decidable.Additive`: the
-- exclusion is not an extra obligation, it is `contra`.
linDecision : Decision Lin (¬G Lin)
linDecision = decDefault Lin linear?

-- EXTERNALISE LATE.  The `Bool` is the GENERIC `okA` applied to the
-- decision, never a separate `accepts : Term• → Bool`.
linearB : ⊤G ⊢ Δ Bool
linearB = okA Lin (¬G Lin) ∘g linear?

-- ==================================================================
-- THE SAME COALGEBRA, RUN AT A SECOND ALGEBRA.  `dbCase` is written
-- once, in `DB.agda`, and is the ONLY thing in the pipeline that ever
-- looks at a de Bruijn constructor; anything else recursive over de
-- Bruijn terms is a new ALGEBRA and nothing more.  Here, the size, as a
-- semantic action -- three lines, no recursion, no termination argument.
-- ==================================================================

ΔN : TmG
ΔN = Δ {s = tm} ℕ

SizeFam : Fam
SizeFam _ = ΔN

private
  sizeStep : DBStep ΔN ⊢ ΔN
  sizeStep =
    ⊕-E (dvar-elim λ n i _ → 1 , tt)
   (⊕-E (dapp-elim λ n u v a b → suc (a .fst + b .fst) , tt)
        (dlam-elim λ n b _ a → suc (a .fst) , tt))

  sizeAlg : Algᴳ DBF SizeFam
  sizeAlg tt = sizeStep ∘g ⟦DB⟧ {M = ⌞ SizeFam ⌟}

sizeA : ⊤G ⊢ ΔN
sizeA = runAut (guarded→LC dbGuarded) dbCase sizeAlg tt
