{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE FUNDAMENTAL THEOREM OF ARITHMETIC AS A PARSING THEOREM.

  ------------------------------------------------------------------
  The framing, and why it is the right one.
  ------------------------------------------------------------------

  A grammar over the Dirichlet promodel is a family indexed by a
  positive integer; a `μ` of a description is a grammar defined by a
  recursion whose recursive slots sit at the parts of a splitting, i.e.
  at DIVISORS.  Because `deg n = n` (Graded.agda), the framework's Löb
  recursion over "strictly smaller degree" is literally strong induction
  on the natural number, and the promodel restricts it to divisors.  So

      Löb over the Dirichlet promodel  =  strong induction on divisors,

  and "a canonical factorisation of n" is not an auxiliary construction
  but the parse tree of n against the grammar

      Fact k  =  ⌈1⌉  ⊕  ⊕ᴰ[ p prime, p ≥ k ] ( ⌈p⌉ ⊗ Fact p ).

  Read that as a context-free grammar over the alphabet of primes, where
  "concatenation" is multiplication.  The index k is a lower bound on the
  primes still allowed: it is what forces the factors to come out in
  nondecreasing order, and hence what makes the grammar UNAMBIGUOUS.
  Without it, `⌈1⌉ ⊕ ⊕ᴰ[p] (⌈p⌉ ⊗ Fact)` would parse 6 twice, as 2·3 and
  as 3·2.  With it, 6 has exactly one parse.  This is exactly the reason
  a grammar for balanced strings is written with an explicit nesting
  discipline rather than as `ε ⊕ (Dyck ⊗ Dyck)`.

  Then the two halves of the fundamental theorem are two standard
  properties of a grammar:

      EXISTENCE   =  totality of `hyloC` -- every n has a parse.
      UNIQUENESS  =  unambiguity of the grammar -- it has at most one.

  and the classical Euler product

      ζ  =  ⊗ᴰ_p  ⌈p⌉*

  is the closed form of the very same grammar: the unique factorisation
  theorem says the canonical-factorisation grammar is isomorphic to ⊤,
  which in the convolution algebra is the statement that ζ factors as an
  infinite ⊗ of Kleene stars, one per prime.  `KL*` at this promodel is
  `μ` of `⌈1⌉ ⊕ (⌈p⌉ ⊗ Var)` -- the same description with the ⊕ᴰ over
  primes deleted -- and it is guarded for exactly the reason the string
  Kleene star is guarded: `⌈p⌉` is "non-nullable", which here means p ≥ 2.

  ------------------------------------------------------------------
  What is proved here, and what is not.
  ------------------------------------------------------------------

  PROVED, with no holes:

    * the grammar, as a generic `μ` over a description built from
      `⌜_⌝`, `⊕e`, `⊗e`, `Var` -- not a hand-written datatype;
    * `factGuarded`, the guardedness certificate, which is the real
      structural content: the recursive slot sits at n/p and p ≥ 2, so
      `Proper` holds and the recursion descends;
    * the `hyloC` wiring, with the algebra run at the SPECIFICATION
      (`Fact` below) rather than at a bare output type, so the
      factorisation comes out already carrying its own correctness proof
      -- the Quicksort trick, and the reason `factorize` cannot be
      written wrongly;
    * the constructors `one-f` / `mul-f` and the destructor `unroll-f`,
      so the grammar can be used without touching `Sh`/`Pos`.

  PARKED as one hole, with its `⊢` type stated:

    * `lpf`, "split off the least prime factor ≥ k".  This is the single
      genuine COMPUTATION in the file, and it is number theory rather
      than grammar theory -- a bounded search for the least divisor ≥ 2,
      plus one transport (associativity of `Times`).  See the long
      comment at `lpf` for the exact decomposition; nothing structural
      depends on it, and the worked parse at the bottom of the file
      exercises the rest of the machinery without it.

  ------------------------------------------------------------------
  PHASE.  `IsPrime`, `NoSmall`, and `lpf` are phase-1 primitives, each with
  a `⊢` type or an explicitly stated shape.  `into` is pure plumbing
  between two spellings of one type (as `intoQ` is in Bags/Quicksort:
  descriptions carry a `Lift` on constants and their slot family is not
  `if`-shaped).  `fcoalg`, `falg`, `factorize` are phase 2: they are
  composites of `∘g`, `⊕-elim`, `⊕ᴰ-in`, `⊕ᴰ-elim`, `liftg`, `⊗I`, `⊗E`
  and the primitives.  No number is ever matched on outside phase 1.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Dirichlet.Factorization where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Mod
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.SemanticAction using (Case; passes; _↦_; _at_)

open import TheoryGrammar.Instances.Dirichlet.Graded public

-- ==================================================================
-- Primes.  Irreducibility is stated with the SUBSTRATE'S OWN
-- splittings: p is prime when every factorisation of it has a unit on
-- one side.  `IsUnit` is the recursive "= 1" predicate from Base.
-- ==================================================================

IsPrime : ℕ₊ → Type₀
IsPrime p = (2 ≤ val p)
          × ((d e : ℕ₊) → Times (val d) (val e) (val p)
             → IsUnit (val d) ⊎ IsUnit (val e))

Prime : Type₀
Prime = Σ[ p ∈ ℕ₊ ] IsPrime p

-- the alphabet at stage k: primes we are still allowed to use
P≥ : ℕ → Type₀
P≥ k = Σ[ p ∈ ℕ₊ ] (IsPrime p × (k ≤ val p))

pv : {k : ℕ} → P≥ k → ℕ₊
pv pp = pp .fst

forget : {k : ℕ} → P≥ k → Prime
forget pp = pp .fst , pp .snd .fst

-- ==================================================================
-- THE GRAMMAR, as a description.  Nonterminals are indexed by ℕ: the
-- nonterminal `k` is "a factorisation using only primes ≥ k".
-- ==================================================================

factSlot : ℕ₊ → Bool → Functor tt
factSlot p true  = ⌜ ⌈ p ⌉ ⌝            -- the prime itself
factSlot p false = Var (val p)          -- the rest, bounded below by p

factAlt : (k : ℕ) → Bool → Functor tt
factAlt k true  = ⌜ δ ⌝                                        -- n = 1
factAlt k false = ⊕e (P≥ k) (λ pp → ⊗e mulop (factSlot (pv pp)))

factF : (k : ℕ) → Functor tt
factF k = ⊕e Bool (factAlt k)

Factorisation : ℕ → Gr
Factorisation k n = μ factF (k , n)

-- ==================================================================
-- GUARDEDNESS.  The one strict step is the ⊗e: the recursive slot holds
-- n/p, and its complement holds p, which is ≥ 2 -- so `Proper` holds
-- and `slotProper` discharges it.  Line for line the same shape as
-- `starGuarded` in Instances/Strings/KleeneStar and `decompGuarded` in
-- Instances/Strings/Decomposition; the ONLY instance-specific input is
-- `ge2NU`, "a number ≥ 2 is a non-unit", proved once in Graded.
-- ==================================================================

factGuarded : (k : ℕ) → Guarded (factF k)
factGuarded k = <⊕e Bool (factAlt k) alt
  where
    go : (pp : P≥ k) (m : ℕ₊) (sp : DirSplit mulop m)
         (sh : (a : Bool) → Sh (factSlot (pv pp) a) (DirParts mulop m sp a))
         (a : Bool) (q : Pos (factSlot (pv pp) a) _ (sh a))
       → degIx (nx (factSlot (pv pp) a) _ (sh a) q) < val m
    go pp m sp sh true ()
    go pp m (d , e , t) sh false q =
      slotProper mulop m (d , e , t) false (≤Var (val (pv pp)))
                 (isP (lower (sh true))) (sh false) q
      where
        isP : d Eq.≡ pv pp → NonUnit d
        isP Eq.refl = ge2NU (pv pp) (pp .snd .fst .fst)

    alt : (b : Bool) → Guarded (factAlt k b)
    alt true  = <⌜⌝ δ
    alt false = <⊕e (P≥ k) _ (λ pp → ⊗-guard mulop (factSlot (pv pp)) (go pp))

-- ==================================================================
-- Constructors and destructor for the grammar, so nothing downstream
-- has to see `Sh`/`Pos`.  (`roll-f` is the algebra, point-free.)
-- ==================================================================

module _ {k : ℕ} where

  one-f : δ ⊢ Factorisation k
  one-f n e = sup (true , lift e) λ ()

  mul-f : (pp : P≥ k) → (⌈ pv pp ⌉ ⊗' Factorisation (val (pv pp))) ⊢ Factorisation k
  mul-f pp n ((d , e , t) , h) =
    sup (false , pp , (d , e , t) , λ { true → lift (h true) ; false → tt* })
        λ { (true , ()) ; (false , _) → h false }

  unroll-f : Factorisation k
           ⊢ (δ ⊕ ⊕ᴰ (P≥ k) (λ pp → ⌈ pv pp ⌉ ⊗' Factorisation (val (pv pp))))
  unroll-f n t with unroll t
  ... | (true  , e)            , f = inl (lower e)
  ... | (false , pp , sp , sh) , f =
    inr (pp , sp , λ { true → lower (sh true) ; false → f (false , tt*) })

  roll-f : (δ ⊕ ⊕ᴰ (P≥ k) (λ pp → ⌈ pv pp ⌉ ⊗' Factorisation (val (pv pp))))
         ⊢ Factorisation k
  roll-f = ⊕-elim one-f (⊕ᴰ-elim mul-f)

-- ==================================================================
-- THE COALGEBRA.
--
-- The carrier is not `⊤`.  It cannot be: `μ factF (k , n)` is inhabited
-- only when every prime factor of n is ≥ k, so a coalgebra at `⊤` would
-- be claiming that every (k , n) is factorable with primes ≥ k, which is
-- false.  The carrier is therefore the invariant itself, and the fact
-- that the framework FORCES you to name it is worth noticing: the
-- coalgebra carrier of a hylomorphism is exactly the loop invariant of
-- the corresponding imperative search.
-- ==================================================================

{-
  THE INVARIANT.  Two candidates present themselves:

      Above  k n  =  every PRIME factor of n is ≥ k
      NoSmall k n  =  every factor of n that is ≥ 2 is ≥ k
                      (equivalently: n has no divisor in [2,k))

  They are equivalent, but not symmetrically so: NoSmall ⟹ Above is
  immediate (a prime factor is a factor ≥ 2), while Above ⟹ NoSmall goes
  through "every number ≥ 2 has a prime factor", which is the very
  theorem being proved.  So `NoSmall` is the right choice, and choosing
  it is what shrinks the remaining work:

    * it is VACUOUS at k = 0, so the top-level call needs no input;
    * it is what makes the least admissible divisor PRIME, without any
      prior theory of primes -- see the hole comment below;
    * it is re-established at the cofactor by the same minimality
      argument, again with no new number theory.

  This is worth recording as a design fact about the framework: the
  coalgebra carrier of a `hyloC` is the loop invariant of the
  corresponding search, and the framework forces you to name it before
  you can even state the search.  Picking the strong-but-cheap invariant
  rather than the semantically obvious one is a decision the type made
  visible.
-}
NoSmall : ℕ → Gr
NoSmall k n = (d e : ℕ₊) → Times (val d) (val e) (val n) → 2 ≤ val d → k ≤ val d

Inv : Ix → Type₀
Inv (k , n) = NoSmall k n

-- vacuous at the bottom of the bound lattice
noSmall0 : (n : ℕ₊) → NoSmall 0 n
noSmall0 n d e t ge = zero-≤

-- and it does imply the semantically obvious statement
NoSmall→Above : {k : ℕ} {n : ℕ₊} → NoSmall k n
              → (p : ℕ₊) → IsPrime p → (e : ℕ₊)
              → Times (val p) (val e) (val n) → k ≤ val p
NoSmall→Above ns p pr e t = ns p e t (pr .fst)

{-
  PRIMITIVE (phase 1) -- PARKED AS A HOLE.

  `lpf k` is "split off the least admissible divisor".  It is the only
  genuine COMPUTATION in the development, and the only thing between here
  and a closed proof of the fundamental theorem.  With `NoSmall` as the
  invariant it decomposes as follows.  Given n with `NoSmall k n`:

    (i)   if n = 1, take the left injection;
    (ii)  otherwise search for the LEAST d with 2 ≤ d and d ∣ n.  It
          exists, since d = n qualifies, and the search is bounded by n.
          This needs decidable divisibility -- `n mod d ≡ 0` via
          Cubical.Data.Nat.Mod -- and a least-witness principle;
    (iii) d ≥ k, directly from the incoming `NoSmall k n`;
    (iv)  d is PRIME: if d = a · b with a , b ≥ 2 then a ∣ n and
          2 ≤ a < d, contradicting minimality in (ii).  Note that this
          uses nothing about primes -- the invariant does the work;
    (v)   the cofactor e = n/d satisfies `NoSmall d e`: a factor c of e
          with c ≥ 2 is a factor of n with c ≥ 2, so c ≥ d by minimality.

  (iv) and (v) both need ASSOCIATIVITY of `Times` -- from `Times a b d`
  and `Times d e n`, produce `Times a (b · e) n` -- which is `·-assoc`
  transported across `timesPath`/`timesAll`, i.e. the same one-line
  pattern as `timesSwap` in Divisors.agda.

  So what is missing is (ii), the bounded search with its minimality
  certificate, plus the transport in (iv)/(v).  Perhaps 150 lines of
  arithmetic, none of it about the calculus.  EVERYTHING STRUCTURAL --
  the grammar, `factGuarded`, the `hyloC` wiring, the specification-
  valued algebra, and the worked parse at the bottom of this file -- is
  independent of this hole.
-}
-- ==================================================================
-- THE ONE COMPUTATION.  Decidable divisibility, and the least divisor
-- ≥ 2 by bounded search.  All arithmetic; nothing here is about the
-- calculus, which is exactly why it sat apart from everything else.
-- ==================================================================

private
  nzPlus2 : (j : ℕ) → NonZero (j + 2)
  nzPlus2 zero    = tt
  nzPlus2 (suc j) = tt

  nz2≤ : {d : ℕ} → 2 ≤ d → NonZero d
  nz2≤ (j , p) = subst NonZero p (nzPlus2 j)

  -- a cofactor of something ≥ 2 cannot be 0
  nzCofactor : {a b c : ℕ} → Times a b c → 2 ≤ c → NonZero b
  nzCofactor {a} {zero}  t 2c =
    E.rec (¬-<-zero (subst (2 ≤_) (sym (timesPath t) ∙ ·-comm a 0) 2c))
  nzCofactor {a} {suc b} t 2c = tt

  -- (c·f = e) and (d·e = n)  ⟹  c·(f·d) = n.  This is step (iv)/(v) of
  -- the plan: a factor of the COFACTOR is a factor of the whole.
  tSwap : {a b c : ℕ} → Times a b c → Times b a c
  tSwap {a} {b} {c} t = subst (Times b a) (·-comm b a ∙ timesPath t) (timesAll b a)

  timesAssoc : {c f e d n : ℕ} → Times c f e → Times d e n → Times c (f · d) n
  timesAssoc {c} {f} {e} {d} {n} tcf tde =
    subst (Times c (f · d)) pf (timesAll c (f · d))
    where
      pf : c · (f · d) ≡ n
      pf = ·-assoc c f d ∙ cong (_· d) (timesPath tcf)
         ∙ ·-comm e d ∙ timesPath tde

  -- DECIDABLE DIVISIBILITY, straight from the division algorithm.  The
  -- refutation is the interesting half: if `d` did divide `n` then
  -- `n mod d` would be `(e · d) mod d`, which is 0.
  divides? : (d n : ℕ) → Dec (Σ[ e ∈ ℕ ] Times d e n)
  divides? zero n with discreteℕ n 0
  ... | yes p = yes (0 , subst (Times 0 0) (sym p) tzero)
  ... | no ¬p = no λ { (e , tzero) → ¬p refl }
  divides? (suc d') n with discreteℕ (n mod suc d') 0
  ... | yes r0 =
    yes ( quotient n / suc d'
        , subst (Times (suc d') (quotient n / suc d'))
                ( cong (_+ (suc d' · (quotient n / suc d'))) (sym r0)
                ∙ ≡remainder+quotient (suc d') n )
                (timesAll (suc d') (quotient n / suc d')) )
  ... | no ¬r0 =
    no λ { (e , t) → ¬r0 ( cong (_mod suc d') (sym (timesPath t))
                         ∙ cong (_mod suc d') (·-comm (suc d') e)
                         ∙ zero-charac-gen (suc d') e ) }

  -- The least factor ≥ 2, with its minimality certificate.  Minimality
  -- is what makes the factor PRIME without any theory of primes, and
  -- what re-establishes `NoSmall` on the cofactor.
  record LF (n : ℕ) : Type₀ where
    constructor mkLF
    field
      lfd lfe : ℕ
      lf2≤    : 2 ≤ lfd
      lfT     : Times lfd lfe n
      lfLeast : (c f : ℕ) → Times c f n → 2 ≤ c → lfd ≤ c

  -- Linear search upward from `j`, carrying "nothing in [2,j) divides n".
  -- The fuel is bounded by `n`, and when it runs out `j ≡ n`, which is
  -- fine because `n` divides itself.
  search : (n j : ℕ) → 2 ≤ n → 2 ≤ j
         → ((c f : ℕ) → Times c f n → 2 ≤ c → j ≤ c)
         → (fuel : ℕ) → n ≤ j + fuel → LF n
  search n j 2n 2j inv zero le =
    mkLF n 1 2n (times1R n) (λ c f t 2c → subst (_≤ c) j≡n (inv c f t 2c))
    where
      j≡n : j ≡ n
      j≡n = ≤-antisym (inv n 1 (times1R n) 2n) (subst (n ≤_) (+-zero j) le)
  search n j 2n 2j inv (suc fuel) le with divides? j n
  ... | yes (e , t) = mkLF j e 2j t inv
  ... | no ¬d =
    search n (suc j) 2n (≤-suc 2j) inv' fuel (subst (n ≤_) (+-suc j fuel) le)
    where
      inv' : (c f : ℕ) → Times c f n → 2 ≤ c → suc j ≤ c
      inv' c f t 2c with ≤-split (inv c f t 2c)
      ... | inl j<c = j<c
      ... | inr j≡c = E.rec (¬d (f , subst (λ z → Times z f n) (sym j≡c) t))

  leastFactor : (n : ℕ) → 2 ≤ n → LF n
  leastFactor n 2n =
    search n 2 2n ≤-refl (λ c f t 2c → 2c) n (≤-suc (≤-suc ≤-refl))

-- ==================================================================
-- ... and the primitive itself.  Matching on the carrier is what makes
-- this phase 1; every consumer below is a composite of combinators.
-- ==================================================================

lpf : (k : ℕ)
    → NoSmall k ⊢ (δ ⊕ ⊕ᴰ (P≥ k) (λ pp → ⌈ pv pp ⌉ ⊗' NoSmall (val (pv pp))))
lpf k (zero , ()) ns
lpf k (suc zero , tt) ns = inl (tt , λ ())
lpf k (suc (suc m) , tt) ns = go (leastFactor N 2≤N)
  where
    N : ℕ
    N = suc (suc m)

    2≤N : 2 ≤ N
    2≤N = suc-≤-suc (suc-≤-suc zero-≤)

    -- Destructured rather than projected: `leastFactor` is defined by a
    -- `with` on the divisibility test, so `LF.lfd (leastFactor …)` is a
    -- stuck term and nothing depending on it would reduce.  Matching the
    -- record once puts plain variables in scope instead.
    go : LF N
       → (δ ⊕ ⊕ᴰ (P≥ k) (λ pp → ⌈ pv pp ⌉ ⊗' NoSmall (val (pv pp))))
           (suc (suc m) , tt)
    go (mkLF d e 2≤d t least) = inr (pp , payload)
      where
        dp ep : ℕ₊
        dp = d , nz2≤ 2≤d
        ep = e , nzCofactor t 2≤N

        -- (iv) THE LEAST FACTOR IS IRREDUCIBLE, and minimality is the
        -- whole proof: if it split as a·b with both sides ≥ 2 then `a`
        -- would also divide N (that is `timesAssoc`) and be strictly
        -- smaller, which the minimality certificate forbids.  No prior
        -- theory of primes is used anywhere.
        irred : (a b : ℕ₊) → Times (val a) (val b) d
              → IsUnit (val a) ⊎ IsUnit (val b)
        irred (zero , ()) b tab
        irred (suc zero , _) b tab = inl tt
        irred (suc (suc a') , _) (zero , ()) tab
        irred (suc (suc a') , _) (suc zero , _) tab = inr tt
        irred (suc (suc a') , nza) (suc (suc b') , nzb) tab =
          E.rec (¬m<m (≤-trans a<d d≤a))
          where
            2a : 2 ≤ suc (suc a')
            2a = suc-≤-suc (suc-≤-suc zero-≤)
            2b : 2 ≤ suc (suc b')
            2b = suc-≤-suc (suc-≤-suc zero-≤)
            a<d : suc (suc a') < d
            a<d = degLtL (suc (suc a') , nza) (suc (suc b') , nzb) dp tab 2b
            d≤a : d ≤ suc (suc a')
            -- note the SWAP: here `tab` lands at `d`, so the outer
            -- factorisation must be read as e·d = N rather than d·e = N
            d≤a = least (suc (suc a')) (suc (suc b') · e)
                        (timesAssoc tab (tSwap t)) 2a

        -- (iii) the least factor is ≥ k, from the invariant coming in
        pp : P≥ k
        pp = dp , ((2≤d , irred) , ns dp ep t 2≤d)

        -- (v) the cofactor inherits the invariant, at the sharper bound d
        nsE : NoSmall d ep
        nsE c f tcf 2c = least (val c) (val f · d) (timesAssoc tcf t) 2c

        payload : (⌈ dp ⌉ ⊗' NoSmall d) (suc (suc m) , tt)
        payload = ⊗-mk dp ep t Eq.refl nsE

-- Plumbing between two spellings of one type.  Pure coercion: the
-- description carries a `Lift` on the representable and its slot family
-- is `factSlot`, not `if`.  Compare `intoQ` in Bags/Quicksort.
into : (k : ℕ) (pp : P≥ k)
     → (⌈ pv pp ⌉ ⊗' NoSmall (val (pv pp)))
     ⊢ ⟦ ⊗e mulop (factSlot (pv pp)) ⟧c Inv
into k pp n =
  ⊗E {P = λ a → (if a then ⌈ pv pp ⌉ else NoSmall (val (pv pp)))} {n = n}
     (λ d e t pf inv →
        ⊗I {P = λ a → ⟦ factSlot (pv pp) a ⟧c Inv} d e t (lift pf) inv)

-- THE COALGEBRA, point-free.
fcoalg : CoalgC factF Inv
fcoalg k =
  ⊕-elim (⊕ᴰ-in true ∘g liftg)
         (⊕ᴰ-elim (λ pp → ⊕ᴰ-in false ∘g ⊕ᴰ-in pp ∘g into k pp))
  ∘g lpf k

-- ==================================================================
-- THE ALGEBRA, RUN AT THE SPECIFICATION.
--
-- The motive IS the statement to be proved: "a list of primes whose
-- product is n".  Nothing is rechecked afterwards -- the algebra emits
-- the proof as it builds the list, so a wrong implementation does not
-- typecheck.  This is `qalgV` from Bags/Quicksort, at a different theory.
-- ==================================================================

prod : List Prime → ℕ
prod []       = 1
prod (p ∷ ps) = val (p .fst) · prod ps

Fact : Ix → Type₀
Fact (k , n) = Σ[ ps ∈ List Prime ] (prod ps ≡ val n)

-- PRIMITIVE (phase 1): the empty product.
oneFact : (n : ℕ₊) → δ n → Fact (0 , n)
oneFact (zero , ())
oneFact (suc zero , _)     _        = [] , refl
oneFact (suc (suc m) , _) (() , _)

-- PRIMITIVE (phase 1): cons, carrying the product equation along.
consFact : (p : Prime) (d e n : ℕ₊)
         → Times (val d) (val e) (val n) → d Eq.≡ (p .fst)
         → Fact (0 , e) → Fact (0 , n)
consFact p d e n t Eq.refl f =
  (p ∷ f .fst) , (cong (val (p .fst) ·_) (f .snd) ∙ timesPath t)

falg : AlgC factF Fact
falg k =
  ⊕ᴰ-elim λ { true  → λ n t → oneFact n (lower t)
            ; false → ⊕ᴰ-elim λ pp → λ n t →
                ⊗E {P = λ a → ⟦ factSlot (pv pp) a ⟧c Fact} {n = n}
                   (λ d e s pf inner →
                      consFact (forget pp) d e n s (lower pf) inner) t }

-- ==================================================================
-- THE THEOREM.  Existence of a prime factorisation IS the totality of
-- the hylomorphism; the guardedness certificate is what makes it total,
-- and the specification-valued algebra is what makes it correct.
-- ==================================================================

factorize : (k : ℕ) (n : ℕ₊) → NoSmall k n → Σ[ ps ∈ List Prime ] (prod ps ≡ val n)
factorize k n inv = hyloC factGuarded fcoalg falg (k , n) inv

fundamentalTheorem : (n : ℕ₊) → Σ[ ps ∈ List Prime ] (prod ps ≡ val n)
fundamentalTheorem n = factorize 0 n (noSmall0 n)

-- ==================================================================
-- A WORKED PARSE, independent of the parked primitive.
--
-- `factorize` is blocked on `lpf`, which is the SEARCH.  Everything
-- else -- the grammar, its constructors, the specification-valued
-- algebra -- is closed, and this section exhibits that by parsing a
-- number by hand and reading the parse back through `falg`.  What comes
-- out is the factorisation together with its correctness proof, and it
-- reduces: the final `refl` is the evaluation.
-- ==================================================================

-- `fold` at a connective-form algebra is the GENERIC `Inductive.foldC`;
-- this file used to re-derive it (as did `Lambda.Passes.Framework`,
-- `Lambda.DeBruijn` and `SimplyTyped.Unique`).
factorise : (i : Ix) → μ factF i → Fact i
factorise = foldC Fact falg

-- Everything ≥ 2 whose value is ≤ 3 is irreducible, because two factors
-- ≥ 2 already multiply to ≥ 4.  Enough for 2 and 3.
mulGe4 : (d'' e'' : ℕ) → 4 ≤ suc (suc d'') · suc (suc e'')
mulGe4 d'' e'' =
  suc-≤-suc (suc-≤-suc (≤-trans (suc-≤-suc (suc-≤-suc zero-≤)) ≤SumRight))

irr≤3 : (p : ℕ₊) → val p ≤ 3
      → (d e : ℕ₊) → Times (val d) (val e) (val p)
      → IsUnit (val d) ⊎ IsUnit (val e)
irr≤3 p le (zero , ())
irr≤3 p le (suc zero , _)        e                  t = inl tt
irr≤3 p le (suc (suc d'') , _) (zero , ())
irr≤3 p le (suc (suc d'') , _) (suc zero , _)       t = inr tt
irr≤3 p le (suc (suc d'') , _) (suc (suc e'') , _)  t =
  E.rec (¬m<m (≤-trans (≤-trans (mulGe4 d'' e'') (≤-reflexive (timesPath t))) le))

prime2 : Prime
prime2 = (2 , tt) , (≤-refl , irr≤3 (2 , tt) (1 , refl))

prime3 : Prime
prime3 = (3 , tt) , ((1 , refl) , irr≤3 (3 , tt) ≤-refl)

at : {k : ℕ} (p : Prime) → k ≤ val (p .fst) → P≥ k
at p le = p .fst , (p .snd , le)

-- 12 = 2 · 2 · 3, as a parse tree against `Factorisation 0`.
parse12 : Factorisation 0 (12 , tt)
parse12 =
  mul-f (at prime2 zero-≤) (12 , tt)
        (⊗-mk (2 , tt) (6 , tt) (timesAll 2 6) Eq.refl
          (mul-f (at prime2 ≤-refl) (6 , tt)
                 (⊗-mk (2 , tt) (3 , tt) (timesAll 2 3) Eq.refl
                   (mul-f (at prime3 (1 , refl)) (3 , tt)
                          (⊗-mk (3 , tt) (1 , tt) (times1R 3) Eq.refl
                            (one-f (1 , tt) δ-mk))))))

-- ... and reading it back through the specification-valued algebra
-- produces the list of primes, with its own proof that they multiply
-- back to 12.  Both halves compute.
_ : passes ( factorise (0 , (12 , tt)) parse12 .fst
               ↦ (prime2 ∷ prime2 ∷ prime3 ∷ [])
           ∷ [] )
_ = refl
