{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SIMULATION INTERFACE: WHAT IT WOULD MEAN FOR A BACKEND TO BE
  CORRECT, AND WHY NO BACKEND IN THIS REPOSITORY IS.

  This is the file the rest of `Compile/` has been missing, and its
  main content is a negative result stated precisely enough to be
  actionable.

  ------------------------------------------------------------------
  1.  THE SITUATION
  ------------------------------------------------------------------

  There are three backends for the linear λ-calculus:

      Compile/LinToISA/Codegen      compileU    : Usage → Program
      Compile/LinToC/Codegen        compileC    : Usage → CProg
      Compile/LinToRust/Alloc/…     compileRust : Usage → RustProg

  and one heap model, `LinLam/Codegen`, with `layout : Usage → Heap`.
  Each proves a real theorem.  `LinToISA`'s is a Hoare triple

      compileTriple : (u : Usage) → ⟪ ⌈ [] ⌉ ⟫ compileU u ⟪ ⌈ layout u ⌉ ⟫ᵖ

  and `LinLam/Codegen`'s is that `layout` is a STRONG monoidal map of
  partial commutative monoids, so a context splitting becomes a
  disjoint heap splitting and the emitted regions cannot alias.  Those
  are theorems about MEMORY LAYOUT, and they are correct.

  Now read the types again.  Every one of them is a function of the
  USAGE.  The compilers are exposed to the calculus as

      compile : {B : Ctx} → B ⊢ Obj
      compile u _ = ⊕ᴰ-I _ (compileU u) u (compileTriple u)

  -- parametric in the grammar `B`, and its second argument is
  discarded.  A term of that type factors through `⊤G`: it is
  `compileAt ⊤G ∘g ⊤-I`, and `compileTm = compile` is an INSTANCE of a
  map that never saw a term.  So the existing correctness theorems are
  satisfied by a compiler that reads only the free-variable set of its
  input and emits nothing for the computation.  `idLin` and `selfApp`
  are closed, they compile to the empty program, and both triples hold.

  That is not a bug in those files -- they say what they prove.  It is
  that "the compiled code computes what the term means" has not been a
  STATABLE proposition, because there was no meaning to compare
  against.  `Normalise.agda` supplies one.  This file supplies the
  square.

  ------------------------------------------------------------------
  2.  THE INTERFACE
  ------------------------------------------------------------------

  A `Backend` is four things: target programs and observations, both
  indexed by the usage (the frame a program runs in is determined by
  the usage -- that is what `layout` says, and it is why the indexing
  is not a cheat); a compiler; a runner; and -- the field that does not
  currently exist anywhere in `Compile/` -- an OBSERVABLE OF A SOURCE
  TERM.  Two squares can then be written:

      Weak    :  run (compile t)  ≡  obs t
      Strong  :  run (compile t)  ≡  obs (nf t)

  `Weak` is what the existing triples are, transposed: `obs t` reads
  off something determined by `t`'s index.  `Strong` is the simulation
  statement -- executing the emitted code agrees with observing THE
  VALUE the source term denotes, `nf t` being that value, total and
  computable by `Normalise.agda`.

  ------------------------------------------------------------------
  3.  THE THREE THEOREMS
  ------------------------------------------------------------------

  (a) `weak↔strong`.  If the observable is USAGE-DIRECTED -- `obs t`
      does not depend on `t`, only on its usage -- then `Weak` and
      `Strong` are interderivable, in both directions.  The proof is
      one line each way, and it uses only that `normalise : TmG ⊢ NfG`
      preserves the usage.  So for a usage-directed observable the
      strong statement carries EXACTLY as much information as the weak
      one, namely none about computation.  This is the precise sense in
      which the existing theorems are not compiler correctness.

  (b) `noBlindBackend`.  A backend whose COMPILER is usage-directed
      (i.e. `compile t ≡ compile t'` whenever `t` and `t'` share a
      usage -- which all three backends satisfy definitionally, their
      compilers being `compileU u` for the index alone) cannot satisfy
      both `Strong` and `Separating`.  `Separating` is adequacy: the
      observable tells distinct normal forms apart.  The witnesses are

          w₁ = x y      w₂ = y x        both at usage  true ∷ true ∷ []

      -- two distinct β-normal terms with the SAME usage, hence the
      same layout `(0,v1) ∷ (1,v1) ∷ []`, the same emitted program, the
      same Hoare triple and the same postcondition.  No amount of
      strengthening the memory-safety argument separates them.

  (c) `adequacy`.  Conversely, `Strong` plus `Separating` says exactly
      that execution DECIDES β-equivalence: `exec t ≡ exec t'` implies
      `nf t ≡ nf t'`.  That is the property one actually wants from a
      compiler, and it is the property to aim at.

  ------------------------------------------------------------------
  4.  VERDICT, AND WHAT WOULD HAVE TO CHANGE
  ------------------------------------------------------------------

  NO EXISTING BACKEND CAN DISCHARGE `Strong` NON-VACUOUSLY, and the
  reason is structural rather than a missing lemma:

    * their compilers have type `{B : Ctx} → B ⊢ Obj` and so cannot
      inspect the term at all;
    * `compileU`, `compileC` and `compileRust` all recurse on the
      USAGE, emitting one allocation per live variable -- `putI i v1`,
      `cdecl i v1`, `letS i v1` -- and never an operation with a data
      dependency;
    * the target `Val` is three-valued and constant (`v1`), chosen so
      that a cell is a reducible closed term.  There is no value
      domain, hence nothing for a source value to be compared with.

  They therefore satisfy `Strong` only in the degenerate way (a)
  describes: `usageBackend` below is the whole family, and it is proved
  here to satisfy `Weak` and `Strong` by `refl` and to fail
  `Separating`.  Recording that is the point -- an honest "no current
  backend satisfies this, because they are usage-directed and emit no
  code for computation" is the finding.

  To discharge the strong statement a backend would have to supply:

    1.  A VALUE DOMAIN in the target and a `⌜_⌝ : Nf u → Value`
        -- a representation of source normal forms.  A closure
        representation suffices; `Val`'s three constants do not.
    2.  A TERM-DIRECTED COMPILER, `compile : ∀ {u} → Tm u → Target u`,
        which by definition cannot be a `{B : Ctx} → B ⊢ Obj`.  This is
        the substantive change: `LinToISA`'s header argues the
        usage-directed compilation is not a shortcut because "a
        term-directed compilation would have to renumber at every
        `tlam`" -- true, and that renumbering is precisely the work a
        real compiler does and this one does not.
    3.  INSTRUCTIONS WITH DATA DEPENDENCIES: an application must emit
        something whose execution depends on what the function part
        evaluated to.  `putI`/`cdecl`/`letS` are all constant stores.
    4.  The square itself, `run (compile t) ≡ ⌜ nf t ⌝`.  With (1)-(3)
        in place this is provable by induction on `size` -- the same
        measure `Size.agda` supplies -- because β on the source side is
        matched by one execution step on the target side and both
        recursions descend on it.

  `refBackend` below shows `Strong` is not vacuous: the identity
  backend, whose target IS the source and whose runner IS `normalise`,
  satisfies it and IS separating.  It also FAILS `Weak` -- so the two
  squares are genuinely different statements, and the weak one is not
  merely a special case.
-}
open import Cubical.Foundations.Prelude

module Compile.Semantics.Simulation where

open import Cubical.Foundations.Function using (idfun)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import Compile.Semantics.Normalise public

private variable ℓ : Level

-- ==================================================================
-- §1  TWO NORMAL FORMS THAT NO USAGE-DIRECTED BACKEND CAN TELL APART.
--
-- `x y` and `y x`, both at usage `true ∷ true ∷ []`.  Same usage, same
-- size, same layout, same emitted program; distinct terms, both
-- β-normal, and not β-convertible.  Everything in §4 turns on them.
-- ==================================================================

w₁ : Tm (true ∷ true ∷ [])                     -- var 0 applied to var 1
w₁ = tapp (uleft (uright unil)) (tvar tt) (tvar tt)

w₂ : Tm (true ∷ true ∷ [])                     -- var 1 applied to var 0
w₂ = tapp (uright (uleft unil)) (tvar tt) (tvar tt)

w₁-nf : Nf w₁
w₁-nf = tt , tt , tt

w₂-nf : Nf w₂
w₂-nf = tt , tt , tt

-- they are already normal, so the semantics fixes them
w₁-fix : nf w₁ ≡ w₁
w₁-fix = refl

w₂-fix : nf w₂ ≡ w₂
w₂-fix = refl

-- ... and they are DISTINCT.  The usage of the function part is the
-- separating observation, and it is one the index can see even though
-- the whole usage cannot: `tapp` carries its splitting.
private
  fnUse : ∀ {u} → Tm u → Usage
  fnUse (tvar _)          = []
  fnUse (tapp {u₁} _ _ _) = u₁
  fnUse (tlam _)          = []

  hd : Usage → Bool
  hd []      = false
  hd (b ∷ _) = b

w₁≢w₂ : ¬ (w₁ ≡ w₂)
w₁≢w₂ p = true≢false (cong (λ t → hd (fnUse t)) p)

-- ==================================================================
-- §2  THE INTERFACE.
--
-- `Target` and `Obs` are indexed by the usage because the frame a
-- program runs in is determined by it -- that is `layout`'s content,
-- and every existing backend's postcondition `⌈ layout u ⌉` already has
-- this shape.  The field that does not exist anywhere in `Compile/` is
-- `obs`: WHAT A SOURCE TERM MEANS, in the target's own vocabulary.
-- ==================================================================

record Backend (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Target  : Usage → Type ℓ
    Obs     : Usage → Type ℓ
    compile : ∀ {u} → Tm u → Target u
    run     : ∀ {u} → Target u → Obs u
    obs     : ∀ {u} → Tm u → Obs u

  -- compile-then-run, the only composite the squares mention
  exec : ∀ {u} → Tm u → Obs u
  exec t = run (compile t)

  -- ----------------------------------------------------------------
  -- THE WEAK SQUARE.  "Running the emitted code produces what the
  -- source term is observed to be."  Every triple in `Compile/` is an
  -- instance, with `obs` reading off the index.
  -- ----------------------------------------------------------------
  Weak : Type ℓ
  Weak = ∀ {u} (t : Tm u) → exec t ≡ obs t

  -- ----------------------------------------------------------------
  -- THE STRONG SQUARE -- SIMULATION.  "Running the emitted code
  -- produces what the source term COMPUTES TO."  `nf` is total and
  -- computable (`Normalise.agda`), so this is a statement about
  -- values, not a Hoare triple: no heap, no separation logic, no
  -- aliasing side conditions.  That is the dividend of putting the
  -- source semantics first.
  -- ----------------------------------------------------------------
  Strong : Type ℓ
  Strong = ∀ {u} (t : Tm u) → exec t ≡ obs (nf t)

  -- the observable sees nothing but the index
  UsageDirected : Type ℓ
  UsageDirected = ∀ {u} (t t' : Tm u) → obs t ≡ obs t'

  -- ... and likewise for the compiler.  This is the property all three
  -- existing backends have DEFINITIONALLY, their compilers being
  -- `compileU u` for the index alone.
  BlindCompiler : Type ℓ
  BlindCompiler = ∀ {u} (t t' : Tm u) → compile t ≡ compile t'

  -- ADEQUACY: the observable tells distinct normal forms apart.  This
  -- is what makes `Strong` say something; without it a backend can be
  -- correct about a semantics nobody can see.
  Separating : Type ℓ
  Separating = ∀ {u} (t t' : Tm u) → Nf t → Nf t' → obs t ≡ obs t' → t ≡ t'

-- ==================================================================
-- §3  WEAK AND STRONG COINCIDE EXACTLY WHEN THE OBSERVABLE IS BLIND.
--
-- Both directions.  The only input is that `normaliseG : TmG ⊢ NfG`
-- preserves the usage, so `nf t` and `t` are comparable at all -- which
-- is itself a fact the index gives for free and an untyped calculus
-- does not have.
-- ==================================================================

module _ {ℓ} (B : Backend ℓ) where
  open Backend B

  strong→weak : UsageDirected → Strong → Weak
  strong→weak ud st t = st t ∙ ud (nf t) t

  weak→strong : UsageDirected → Weak → Strong
  weak→strong ud wk t = wk t ∙ ud t (nf t)

  -- ----------------------------------------------------------------
  -- THE PAYOFF.  Correct AND adequate says exactly: EXECUTION DECIDES
  -- β-EQUIVALENCE.  This is the proposition the pipeline wants, and it
  -- is unstatable without a source semantics.
  -- ----------------------------------------------------------------
  adequacy : Strong → Separating
           → ∀ {u} (t t' : Tm u) → exec t ≡ exec t' → nf t ≡ nf t'
  adequacy st sep t t' e =
    sep (nf t) (nf t') (nfNormal t) (nfNormal t')
        (sym (st t) ∙ e ∙ st t')

  -- ----------------------------------------------------------------
  -- THE VERDICT.  A backend that compiles the INDEX cannot be both
  -- correct and adequate.  Note that only the COMPILER is assumed
  -- blind -- the observable may be as rich as one likes; it will never
  -- be reached, because `w₁` and `w₂` are sent to the same program.
  -- ----------------------------------------------------------------
  noBlindBackend : BlindCompiler → Strong → Separating → ⊥
  noBlindBackend blind st sep = w₁≢w₂ (sep w₁ w₂ w₁-nf w₂-nf same)
    where
    sameExec : exec w₁ ≡ exec w₂
    sameExec = cong run (blind w₁ w₂)

    same : obs w₁ ≡ obs w₂
    same = sym (cong obs w₁-fix) ∙ sym (st w₁)
         ∙ sameExec
         ∙ st w₂ ∙ cong obs w₂-fix

-- ==================================================================
-- §4  THE FAMILY EVERY EXISTING BACKEND BELONGS TO.
--
-- `emitU : Usage → O` is `compileU`, `compileC`, `compileRust` and
-- `layout` all at once -- a program (or a heap, or a postcondition)
-- computed from the usage.  Running it is the identity because there
-- is nothing else to do with it, and the source observable can only be
-- the same thing.  This is not a straw man: it is the general form of
-- what `Compile/` currently contains, with the specific target erased.
-- ==================================================================

module _ {ℓ} (O : Type ℓ) (emitU : Usage → O) where

  usageBackend : Backend ℓ
  usageBackend .Backend.Target _   = O
  usageBackend .Backend.Obs    _   = O
  usageBackend .Backend.compile {u} _ = emitU u
  usageBackend .Backend.run        p  = p
  usageBackend .Backend.obs    {u} _  = emitU u

  private module U = Backend usageBackend

  -- it is correct, in both senses, and both proofs are `refl`.  That is
  -- the whole problem: nothing was checked.
  usageWeak : U.Weak
  usageWeak t = refl

  usageStrong : U.Strong
  usageStrong t = refl

  usageBlind : U.BlindCompiler
  usageBlind t t' = refl

  usageUD : U.UsageDirected
  usageUD t t' = refl

  -- ... and it is not adequate, by §3.
  usageNotSeparating : ¬ U.Separating
  usageNotSeparating = noBlindBackend usageBackend usageBlind usageStrong

-- ==================================================================
-- §5  `Strong` IS NOT VACUOUS, AND IT IS NOT `Weak`.
--
-- The reference backend: the target IS the source calculus and running
-- a program IS normalising it.  Trivial as a compiler, but it pins the
-- interface down at both ends -- it satisfies `Strong` and
-- `Separating`, and it FAILS `Weak`.  So the two squares are different
-- propositions and the weak one is not a special case of the strong.
-- ==================================================================

refBackend : Backend ℓ-zero
refBackend .Backend.Target u  = Tm u
refBackend .Backend.Obs    u  = Tm u
refBackend .Backend.compile t = nf t
refBackend .Backend.run     p = p
refBackend .Backend.obs     t = t

private module R = Backend refBackend

-- correct: running the compiled program IS the source value
refStrong : R.Strong
refStrong t = refl

-- adequate: the observable is the term itself
refSeparating : R.Separating
refSeparating t t' _ _ p = p

-- ... and consistent with §3: its compiler is NOT blind, so
-- `noBlindBackend` does not apply.  Exhibited, rather than assumed.
refNotBlind : ¬ R.BlindCompiler
refNotBlind bl = w₁≢w₂ (bl w₁ w₂)

-- the weak square FAILS for it: `nf selfApp ≡ idLin`, not `selfApp`
private
  tag : ∀ {u} → Tm u → Bool
  tag (tvar _)     = false
  tag (tapp _ _ _) = false
  tag (tlam _)     = true

refNotWeak : ¬ R.Weak
refNotWeak wk = true≢false (cong tag (wk selfApp))
