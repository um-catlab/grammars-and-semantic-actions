{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  POSITIONS, AND THE THREE THINGS THAT MOVE THEM.

  `Compile/Relational/Names.agda` is the same file one backend over: the
  source's substitution (`Size.subS`) is not a bare structural
  recursion, it calls `coeTm`, `delT` and `insT`, and before the
  substitution lemma can be stated the relation has to be shown blind to
  all three.  There the target was a term with NAMES and the arithmetic
  was about a name assignment `ν`; here the target reads a FRAME and the
  arithmetic is about slot numbers.  So the content of this file is:

    §1  `LiveAt` / `DeadAt` / `Dif` / `Lt`, all `Unit`/`⊥`-valued, so
        nothing they carry ever blocks a `refl`.

    §2  `Solo` and `slotOf`: a `Solo` usage is live at exactly the
        position `slotOf` names, and at no other.

    §3  `Above k v` -- "everything strictly past `k` is dead".  This is
        the invariant `Correct.agda`'s header §3(b) calls `Last`, in the
        form that PROPAGATES: it is a statement about the USAGE, so it
        survives a splitting without anyone having to match on
        `atSplit`/`delSplit`/`insSplit`.

        It is what makes `delSlot`/`insSlot` true.  Deleting slot `k`
        shifts every position above `k` down by one, and the target
        expression is untouched by the deletion -- so the slot equation
        in `RelE.rvar` would break.  `Above` says there is nothing above
        `k` to shift.  And it holds, for the reason call-by-value at
        closed terms makes it hold: the substituted slot is the LAST
        one, because a closed λ-body is `Tm (true ∷ [])` and `subS`'s
        `tlam` clause descends with `mthere true`, so at depth `d` the
        scope has length `d + 1` and the mark sits at `d`.

    §4  THE IDENTITY CAPTURE IS POSITIONAL.  `Convert.agda`'s header
        claims

            spread u (capVals σ (idCap u))   agrees with   σ

        on every live position of `u`; §4 proves it, together with the
        two facts the frame bookkeeping in `relSubst`'s `rclos` case
        needs -- that a DEAD position reads `junk`, and that `capVals`
        only ever looks at live positions.

  PHASE
  -----

  Phase 1.  Everything is stated in `Eq`-world, for the documented
  reason: these equations are rewritten INSIDE an application of
  `spread`/`σ`, and a cubical `Path` would leave a stuck `transp`.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.Names where

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.ClosureConv.Convert public

-- ==================================================================
-- §1  THE FOUR PREDICATES.
-- ==================================================================

-- PRIMITIVE (phase 1)
LiveAt : ℕ → Usage → Type₀
LiveAt _       []          = ⊥
LiveAt zero    (true  ∷ _) = Unit
LiveAt zero    (false ∷ _) = ⊥
LiveAt (suc p) (_ ∷ u)     = LiveAt p u

-- PRIMITIVE (phase 1)
DeadAt : ℕ → Usage → Type₀
DeadAt _       []          = Unit
DeadAt zero    (true  ∷ _) = ⊥
DeadAt zero    (false ∷ _) = Unit
DeadAt (suc p) (_ ∷ u)     = DeadAt p u

-- PRIMITIVE (phase 1)
Dif : ℕ → ℕ → Type₀
Dif zero    zero    = ⊥
Dif zero    (suc _) = Unit
Dif (suc _) zero    = Unit
Dif (suc m) (suc n) = Dif m n

-- PRIMITIVE (phase 1)
Lt : ℕ → ℕ → Type₀
Lt _       zero    = ⊥
Lt zero    (suc _) = Unit
Lt (suc m) (suc n) = Lt m n

dif-irrefl : (p : ℕ) → Dif p p → ⊥
dif-irrefl zero    d = d
dif-irrefl (suc p) d = dif-irrefl p d

-- a live position and a dead position of the SAME usage are distinct.
-- This is the only place `Dif` is produced, and every frame-agreement
-- side condition below goes through it.
live-dead-dif : (p q : ℕ) (u : Usage) → LiveAt p u → DeadAt q u → Dif p q
live-dead-dif p       q       []          l d = E.rec l
live-dead-dif zero    zero    (true  ∷ u) l d = E.rec d
live-dead-dif zero    zero    (false ∷ u) l d = E.rec l
live-dead-dif zero    (suc q) (c ∷ u)     l d = tt
live-dead-dif (suc p) zero    (c ∷ u)     l d = tt
live-dead-dif (suc p) (suc q) (c ∷ u)     l d = live-dead-dif p q u l d

live-dead : (p : ℕ) (u : Usage) → LiveAt p u → DeadAt p u → ⊥
live-dead p u l d = dif-irrefl p (live-dead-dif p p u l d)

liveDec : (p : ℕ) (u : Usage) → LiveAt p u ⊎ DeadAt p u
liveDec p       []          = inr tt
liveDec zero    (true  ∷ u) = inl tt
liveDec zero    (false ∷ u) = inr tt
liveDec (suc p) (c ∷ u)     = liveDec p u

emptyDead : (u : Usage) → Empty u → (p : ℕ) → DeadAt p u
emptyDead []          e p       = tt
emptyDead (true  ∷ u) e p       = E.rec e
emptyDead (false ∷ u) e zero    = tt
emptyDead (false ∷ u) e (suc p) = emptyDead u e p

-- ==================================================================
-- §2  `Solo` NAMES EXACTLY ONE POSITION, AND `slotOf` IS IT.
-- ==================================================================

soloLiveAt : (u : Usage) (s : Solo u) → LiveAt (slotOf 0 u s) u
soloLiveAt []          ()
soloLiveAt (true  ∷ u) s = tt
soloLiveAt (false ∷ u) s =
  Eq.transport (λ z → LiveAt z (false ∷ u))
    (Eq.sym (slotOf-shift 0 u s)) (soloLiveAt u s)

soloUnique : (u : Usage) (s : Solo u) (p : ℕ) → LiveAt p u → p Eq.≡ slotOf 0 u s
soloUnique []          ()      p       l
soloUnique (true  ∷ u) s       zero    l = Eq.refl
soloUnique (true  ∷ u) s       (suc p) l = E.rec (live-dead p u l (emptyDead u s p))
soloUnique (false ∷ u) s       zero    l = E.rec l
soloUnique (false ∷ u) s       (suc p) l =
  Eq.ap suc (soloUnique u s p l) Eq.∙ Eq.sym (slotOf-shift 0 u s)

-- ------------------------------------------------------------------
-- Splittings move liveness the four ways one expects, and `split-excl`
-- is the linearity lemma at the level of positions: `Use⊎` has no
-- (true,true) constructor, so a position live on one side is DEAD on
-- the other.
-- ------------------------------------------------------------------

split-live : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (p : ℕ)
           → LiveAt p u → LiveAt p u₁ ⊎ LiveAt p u₂
split-live unil        p       l = E.rec l
split-live (uleft  s)  zero    l = inl tt
split-live (uleft  s)  (suc p) l = split-live s p l
split-live (uright s)  zero    l = inr tt
split-live (uright s)  (suc p) l = split-live s p l
split-live (uskip  s)  zero    l = E.rec l
split-live (uskip  s)  (suc p) l = split-live s p l

split-liveL : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (p : ℕ) → LiveAt p u₁ → LiveAt p u
split-liveL unil        p       l = E.rec l
split-liveL (uleft  s)  zero    l = tt
split-liveL (uleft  s)  (suc p) l = split-liveL s p l
split-liveL (uright s)  zero    l = E.rec l
split-liveL (uright s)  (suc p) l = split-liveL s p l
split-liveL (uskip  s)  zero    l = E.rec l
split-liveL (uskip  s)  (suc p) l = split-liveL s p l

split-liveR : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (p : ℕ) → LiveAt p u₂ → LiveAt p u
split-liveR unil        p       l = E.rec l
split-liveR (uleft  s)  zero    l = E.rec l
split-liveR (uleft  s)  (suc p) l = split-liveR s p l
split-liveR (uright s)  zero    l = tt
split-liveR (uright s)  (suc p) l = split-liveR s p l
split-liveR (uskip  s)  zero    l = E.rec l
split-liveR (uskip  s)  (suc p) l = split-liveR s p l

split-deadL : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (p : ℕ) → DeadAt p u → DeadAt p u₁
split-deadL unil        p       d = tt
split-deadL (uleft  s)  zero    d = E.rec d
split-deadL (uleft  s)  (suc p) d = split-deadL s p d
split-deadL (uright s)  zero    d = tt
split-deadL (uright s)  (suc p) d = split-deadL s p d
split-deadL (uskip  s)  zero    d = tt
split-deadL (uskip  s)  (suc p) d = split-deadL s p d

split-deadR : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (p : ℕ) → DeadAt p u → DeadAt p u₂
split-deadR unil        p       d = tt
split-deadR (uleft  s)  zero    d = tt
split-deadR (uleft  s)  (suc p) d = split-deadR s p d
split-deadR (uright s)  zero    d = E.rec d
split-deadR (uright s)  (suc p) d = split-deadR s p d
split-deadR (uskip  s)  zero    d = tt
split-deadR (uskip  s)  (suc p) d = split-deadR s p d

-- THE LINEARITY LEMMA, POSITIONWISE
split-excl : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (p : ℕ) → LiveAt p u₁ → DeadAt p u₂
split-excl unil        p       l = tt
split-excl (uleft  s)  zero    l = tt
split-excl (uleft  s)  (suc p) l = split-excl s p l
split-excl (uright s)  zero    l = E.rec l
split-excl (uright s)  (suc p) l = split-excl s p l
split-excl (uskip  s)  zero    l = E.rec l
split-excl (uskip  s)  (suc p) l = split-excl s p l

split-exclR : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (p : ℕ) → LiveAt p u₂ → DeadAt p u₁
split-exclR unil        p       l = tt
split-exclR (uleft  s)  zero    l = E.rec l
split-exclR (uleft  s)  (suc p) l = split-exclR s p l
split-exclR (uright s)  zero    l = tt
split-exclR (uright s)  (suc p) l = split-exclR s p l
split-exclR (uskip  s)  zero    l = E.rec l
split-exclR (uskip  s)  (suc p) l = split-exclR s p l

-- ==================================================================
-- §3  THE MARKED POSITION, AND WHAT IS ABOVE IT.
-- ==================================================================

-- `Mark true k` marks a LIVE position, and `slotOf` finds it there
markT-slotOf : ∀ {k u v} (m : Mark true k u v) (s : Solo v) → slotOf 0 v s Eq.≡ k
markT-slotOf mhere             s = Eq.refl
markT-slotOf (mthere true  m)  s = E.rec (markT-¬Empty m s)
markT-slotOf (mthere false m)  s =
  slotOf-shift 0 _ s Eq.∙ Eq.ap suc (markT-slotOf m s)

markT-liveAt : ∀ {k u v} (m : Mark true k u v) → LiveAt k v
markT-liveAt mhere        = tt
markT-liveAt (mthere c m) = markT-liveAt m

-- ------------------------------------------------------------------
-- THE INVARIANT.  "Nothing strictly above `k` is live."
--
-- Stated about the USAGE rather than about the `Mark`, which is the
-- whole point: it then transports along a splitting with `split-dead*`
-- and no one has to case on `atSplit`.
-- ------------------------------------------------------------------
Above : ℕ → Usage → Type₀
Above k v = (p : ℕ) → Lt k p → DeadAt p v

above-cons : ∀ {k v} (c : Bool) → Above k v → Above (suc k) (c ∷ v)
above-cons c ab zero    l = E.rec l
above-cons c ab (suc p) l = ab p l

above-splitL : ∀ {k u₁ u₂ u} (s : Use⊎ u₁ u₂ u) → Above k u → Above k u₁
above-splitL s ab p l = split-deadL s p (ab p l)

above-splitR : ∀ {k u₁ u₂ u} (s : Use⊎ u₁ u₂ u) → Above k u → Above k u₂
above-splitR s ab p l = split-deadR s p (ab p l)

above-empty : ∀ {k u} → Empty u → Above k u
above-empty {u = u} e p l = emptyDead u e p

-- ------------------------------------------------------------------
-- ... AND THE TWO EQUATIONS IT BUYS.
--
-- Deleting slot `k` shifts every position above `k` down, and inserting
-- one shifts them up.  With nothing above `k`, both are the identity on
-- slot numbers -- which is exactly what lets `RelE`'s `rvar` equation
-- survive a `delT` or an `insT` with the TARGET untouched.
-- ------------------------------------------------------------------

delSlot : ∀ {k q v} (m : Mark false k q v) → Above k v → (s : Solo v)
        → slotOf 0 q (markF-Solo← m s) Eq.≡ slotOf 0 v s
delSlot (mhere {u = q})    ab s =
  E.rec (live-dead (slotOf 0 q s) q (soloLiveAt q s) (ab (suc (slotOf 0 q s)) tt))
delSlot (mthere true  m)   ab s = Eq.refl
delSlot (mthere false m)   ab s =
    slotOf-shift 0 _ (markF-Solo← m s)
  Eq.∙ Eq.ap suc (delSlot m (λ p l → ab (suc p) l) s)
  Eq.∙ Eq.sym (slotOf-shift 0 _ s)

insSlot : ∀ {k q v} (m : Mark false k q v) → Above k v → (s : Solo q)
        → slotOf 0 v (markF-Solo→ m s) Eq.≡ slotOf 0 q s
insSlot (mhere {u = q})    ab s =
  E.rec (live-dead (slotOf 0 q s) q (soloLiveAt q s) (ab (suc (slotOf 0 q s)) tt))
insSlot (mthere true  m)   ab s = Eq.refl
insSlot (mthere false m)   ab s =
    slotOf-shift 0 _ (markF-Solo→ m s)
  Eq.∙ Eq.ap suc (insSlot m (λ p l → ab (suc p) l) s)
  Eq.∙ Eq.sym (slotOf-shift 0 _ s)

-- ==================================================================
-- §4  THE IDENTITY CAPTURE IS POSITIONAL.
--
-- `Convert.agda` §3 claims this and does not prove it; the `rclos` case
-- of the substitution lemma is where the claim is cashed, because the
-- frame the block runs under has to be recognised as the CALLER's frame
-- shifted by one.
-- ==================================================================

-- prepending a dead slot to the caller's scope shifts every captured
-- position by one
capWkD-shift : ∀ {sh u} (σ : Frame) (c : Cap sh u)
             → capVals σ (capWkD c) Eq.≡ capVals (λ p → σ (suc p)) c
capWkD-shift σ (cnil e)  = Eq.refl
capWkD-shift σ (cdead c) = capWkD-shift σ c
capWkD-shift σ (clive {u₁ = u₁} sp so c) =
    Eq.ap (λ z → σ z ∷ capVals σ (capWkD c)) (slotOf-shift 0 u₁ so)
  Eq.∙ Eq.ap (λ z → σ (suc (slotOf 0 u₁ so)) ∷ z) (capWkD-shift σ c)

-- THE CLAIM: on a LIVE position, reading the block's environment is
-- reading the caller's frame
spreadIdCap : (u : Usage) (σ : Frame) (p : ℕ) → LiveAt p u
            → spread u (capVals σ (idCap u)) p Eq.≡ σ p
spreadIdCap []          σ p       l = E.rec l
spreadIdCap (true  ∷ u) σ zero    l = Eq.refl
spreadIdCap (true  ∷ u) σ (suc p) l =
    Eq.ap (λ z → spread u z p) (capWkD-shift σ (idCap u))
  Eq.∙ spreadIdCap u (λ q → σ (suc q)) p l
spreadIdCap (false ∷ u) σ zero    l = E.rec l
spreadIdCap (false ∷ u) σ (suc p) l =
    Eq.ap (λ z → spread u z p) (capWkD-shift σ (idCap u))
  Eq.∙ spreadIdCap u (λ q → σ (suc q)) p l

-- ... and on a DEAD one it is junk, so two frames that differ only off
-- the live positions build the same environment
spreadIdCapDead : (u : Usage) (σ : Frame) (p : ℕ) → DeadAt p u
                → spread u (capVals σ (idCap u)) p Eq.≡ junk
spreadIdCapDead []          σ p       d = Eq.refl
spreadIdCapDead (true  ∷ u) σ zero    d = E.rec d
spreadIdCapDead (true  ∷ u) σ (suc p) d =
    Eq.ap (λ z → spread u z p) (capWkD-shift σ (idCap u))
  Eq.∙ spreadIdCapDead u (λ q → σ (suc q)) p d
spreadIdCapDead (false ∷ u) σ zero    d = Eq.refl
spreadIdCapDead (false ∷ u) σ (suc p) d =
    Eq.ap (λ z → spread u z p) (capWkD-shift σ (idCap u))
  Eq.∙ spreadIdCapDead u (λ q → σ (suc q)) p d

-- the capture only ever LOOKS at live positions
capValsCong : (u : Usage) (σ₀ σ₁ : Frame)
            → ((p : ℕ) → LiveAt p u → σ₀ p Eq.≡ σ₁ p)
            → capVals σ₀ (idCap u) Eq.≡ capVals σ₁ (idCap u)
capValsCong []          σ₀ σ₁ ag = Eq.refl
capValsCong (true  ∷ u) σ₀ σ₁ ag =
    Eq.ap (λ z → z ∷ capVals σ₀ (capWkD (idCap u))) (ag 0 tt)
  Eq.∙ Eq.ap (λ z → σ₁ 0 ∷ z)
        ( capWkD-shift σ₀ (idCap u)
        Eq.∙ capValsCong u (λ q → σ₀ (suc q)) (λ q → σ₁ (suc q))
               (λ p l → ag (suc p) l)
        Eq.∙ Eq.sym (capWkD-shift σ₁ (idCap u)) )
capValsCong (false ∷ u) σ₀ σ₁ ag =
    capWkD-shift σ₀ (idCap u)
  Eq.∙ capValsCong u (λ q → σ₀ (suc q)) (λ q → σ₁ (suc q))
         (λ p l → ag (suc p) l)
  Eq.∙ Eq.sym (capWkD-shift σ₁ (idCap u))
