# The linear-λ compiler pipeline: roadmap

Reconstructed from file headers on branch `theory-generic-lambekd`. Every
claim below is sourced to a named definition in a file that was read in
full; anything not verifiable that way is marked. This document does not
introduce facts — it collects the phase numbering that currently exists
only as prose in individual headers.

Status of the tree at time of writing: `Instances/LinLam/` and
`Instances/Affine/` are **untracked** (`git status` shows `??`), i.e. not
yet committed on this branch. No file in either directory contains a hole
(`{!`), a `postulate`, or a `{-# TERMINATING #-}` pragma.

---

## 0. Two numbering schemes, and a third. Read this first.

There are **three independent uses of the word "phase"/"pass"** in this
tree. They are unrelated and conflating them is the standing trap.

| scheme | where it is defined | meaning |
|---|---|---|
| **phase 1 / phase 2** (lower case) | `CLAUDE.md`, top of file | *Discipline.* Phase 1 = building the language (may pattern-match the carrier); phase 2 = using it (only `⊢`-combinators). Applies to every line of code in the repository. Nothing to do with the compiler. |
| **PHASE 2 / 3 / 4** (upper case) | `Instances/LinLam/{Context,Opt,Codegen}.agda` headers | *The compiler pipeline.* The subject of this document. |
| **PASS 1 / PASS 2** | `Instances/LinLam/{Scope,Check}.agda` headers | *The front end,* a separate local numbering inside the same directory. |

Two further collisions, both harmless once named:

- `Instances/Lambda/Passes/{Eta,Dead,Inline}.agda` are also labelled
  `PASS 1/2/3` (and indexed as such in `Passes/All.agda`). That is the
  **untyped named-λ** development, which the LinLam headers cite
  repeatedly *for contrast*. It is not a stage of this pipeline.
- `src/Grammar/LambdaPasses.agda` (outside `TheoryGrammar/` entirely) has
  its own `PASS 1. Scoped → de Bruijn` / `PASS 2. Linearity`. It is a
  standalone, pre-promodel file; `LinLam/{Scope,Check}` are the
  in-calculus redoing of exactly those two passes. It is not imported by
  anything in `TheoryGrammar/`.

**There is no file labelled `PHASE 1`.** The pipeline numbering starts at
`PHASE 2`. Section 2 below records what appears to occupy the slot and
flags that identification as inference, not as something a header states.

---

## 1. The pipeline

All paths relative to `src/TheoryGrammar/`.

| # | file | establishes | headline theorem(s), by name |
|---|---|---|---|
| — (front end, "PASS 1"/"PASS 2") | `Instances/LinLam/DB.agda` | Scope-indexed de Bruijn terms as a promodel over `λSig` — the theory the elaborator lands *in*, so that elaboration is a map of promodels rather than an exit from the calculus. Well-scopedness collapses (`In ≡ ⊤G` definitionally) and α-equivalence becomes the absence of a choice in `parts`. | `dbFib`, `dbGrading`, `dbGuarded`, `dbCase` (the decomposition axiom); `dbAll : ⊤G ⊢ DBAll` — every point is well-scoped, proved by the generic `scanμ`, no induction written. |
| PASS 1 | `Instances/LinLam/Scope.agda` | Named → de Bruijn as a `Reindex λFib dbFib`. Total (takes an environment), hence a genuine carrier map. | `dbCM`; `elabScoped : ⊤G ⊢ S.pull DBAll` (a target theorem transported by `pullTerm` alone); `presVar`, `presApp`, `reflVar`, `reflApp` positive; `¬presLam`, `¬reflLam` negative. |
| PASS 2 | `Instances/LinLam/Check.agda` | The linearity checker as an *internal* decision, over `dbFib`. One coalgebra (`dbCase`), two algebras (`linAlg`, `sizeAlg`), recursion by `runAut` = `hyloC` = `löb`. | `linear? : ⊤G ⊢ Dec⟨ Lin ⟩`; `linDecision`; `linUniq`; `linearB` (the `Bool` view, via generic `okA`, externalised late). |
| — | `Instances/LinLam/Tests.agda` | The checker *computes*, and its negative answers are refutations, not observations. | `decisions`, `sizes` (one `refl` each); `no-dup : (¬G Lin) (0 , dupT)`, `no-drop : (¬G Lin) (0 , dropT)`, `is-id : Lin (0 , idT)`. |
| **PHASE 2** (theory) | `Instances/LinLam/Context.agda` | Linear contexts as a partial commutative monoid, presented as a promodel over `monoidSig`. Linearity is the **absent** `(true,true)` constructor of `Use⊎` — structural, no equation, nothing to unfold. Grading by `live` makes `Ind`/`Guard`/`hyloC` available. | `Use⊎`, `linFib`, `_⊛_` (= `⊗ˢ appop`), `nothingLeft`; `noDupUse`; `liveSplit : live u + live v ≡ live w`; `linGrading`, `linGraded`. |
| **PHASE 2** (syntax) | `Instances/LinLam/Syntax.agda` | Linear terms over that promodel. Application **is** the tensor, abstraction **is** reindexing along `u ↦ true ∷ u`; the side condition of the application rule is not discharged because `⊗ˢ` *is* it. | `Tm`; `appT : (TmG ⊛ TmG) ⊢ TmG`; `lamT : (λ u → Tm (true ∷ u)) ⊢ TmG`; `varT`; `Pass = TmG ⊢ TmG`. |
| **PHASE 3** | `Instances/LinLam/Opt.agda` | Optimisation passes as algebras for one fold. β is safe here because linear substitution is a *term*, not a carrier map. DCE is **vacuous as a theorem**. | `foldTm`, `roll`, `foldRollPass : foldTm TmG roll ≡ idPass`; `substT : (BodyOf TmG ⊛ TmG) ⊢ TmG`, `substUP` (Iso: substitution *is* the internal hom), `substIsApp` (holds by `refl`); `budgetEq`; `deadBinder : DeadBinder ⊢ ⊥G`, `dceUnique`; `noSelfSplit`; `betaPass`, `etaPass`, `optimise`. |
| **PHASE 4** | `Instances/LinLam/Codegen.agda` | Code generation as a `Reindex linFib heapFib` into the separation-logic promodel. No-aliasing is `SplitPresAt`, i.e. the pass's **type**. Also proves the negative: the compacting layout fails. | `layoutMap`; `layPres : (o : MonOp) → SplitPresAt layoutMap o`; `layRefl : (o : MonOp) → A.ReflectsSplitAt o`; `lay∗`/`lay∗⁻`, `layEmp`/`layEmp⁻` (strong monoidality); `layFrame`, `noDupLay` (transported); `emit`/`emitTm`; **`noPackPres : SplitPresAt packMap appop → ⊥`**. |

Import graph (so the reading order is unambiguous):

```
Lambda/{Signature,Fibered,Base}      Heap/{Base,Connectives,Graded}
        |                                        |
     LinLam/DB  ──► LinLam/Check ──► LinLam/Scope |
                          |                      |
                          └── uses ──┐           |
                                     v           v
  LinLam/Context ──► LinLam/Syntax ──┼──► LinLam/Opt
                                     └──► LinLam/Codegen
```

`Check.agda` is the one place the two halves meet, and it meets them in
the *metalanguage* — see the `join?` limitation in §4.

---

## 2. The missing Phase 1

No header says `PHASE 1`. What the pipeline plainly needs before
`Context.agda` — and what `Scope`/`Check` actually are — is the front
end: raw named terms over `λFib` (`Instances/Lambda/{Signature,Fibered,
Base}.agda`), elaborated to `dbFib` and certified linear.

Evidence for the identification: `Check.Lin` is *defined* in terms of
`LinLam/Syntax.Tm`, so the front end's output certificate is literally a
Phase-2 term. Evidence against making it official: nothing in any header
calls it Phase 1, and `Scope`/`Check` carry their own `PASS 1`/`PASS 2`
labels instead.

**Treat "Phase 1 = the front end" as this document's inference, not as a
claim of the source.**

---

## 3. The central claim

Stated precisely, from the `Codegen.agda` header (§"THE CLAIM UNDER
TEST") and the `Context.agda` header (§"THE SAME SHAPE AS HEAPS").

Both ends of the compiler are partial commutative monoids presented as
promodels over `monoidSig`, in the *same* shape:

```
LinLam/Context   Split appop u = Σ u₁, Σ u₂, Use⊎ u₁ u₂ u
Heap/Base        Split appop h = Σ h₁, Σ h₂, Ilv h₁ h₂ h × (h₁ # h₂)
```

In the source, linearity is the **absent** constructor: `Use⊎` has no
clause taking `true` on both sides. In the target, partiality is the
**present** `h₁ # h₂` conjunct: two regions may not own a location. The
claim is that

> the source's missing constructor **manufactures** the target's
> disjointness conjunct,

so that "the code emitted for the two premises of an application does not
alias" is not a theorem *about* the pass but the pass's very **type**.

Two facts carry it, and the header states they are the only two:

1. **Positions are addresses** — `freshLay`: everything `lay i u`
   allocates sits at a location `≥ i`, hence apart from any `j < i`. This
   is what turns absence into presence, because the only way `Use⊎` lets
   two slots both reach position `i` is the clause that does not exist.
2. **The offset is shared** — `Use⊎ u₁ u₂ u` puts all three usages in
   lockstep, so `ilvLay` is a constructor-for-constructor translation
   (`uleft ↦ left`, `uright ↦ right`, `uskip ↦ id`, `unil ↦ nil`) with no
   arithmetic in it.

The verdict recorded in the header is that it holds **and more**:

- `layPres` builds `SplitPresAt` at **both** operations (`appop`,
  `nilop`).
- `layRefl` builds `Along.ReflectsSplitAt` at both as well — reflection
  does not even use disjointness; `Ilv` alone reflects.
- Hence splittings correspond **bijectively**, which the header names as
  the discrete Conduché condition of `ChangeOfTheory` read at a promodel.
- Concretely `push⊗`/`pull⊗` (from `Along`, in `CarrierMap.agda`) give
  both halves of `Lay A ⊛ Lay B ⊣⊢ Lay (A ∗ B)` — i.e. the layout is a
  **strong** monoidal functor from linear contexts to separation logic,
  `⊛` (context splitting) to `∗` (heap separation). The terms are
  `lay∗`/`lay∗⁻` at `appop` and `layEmp`/`layEmp⁻` at `nilop`.

The payoff, and the reason this is a pipeline rather than an analogy:
theorems transport. `layFrame` is the separation-logic frame rule
(`H.frame`) pulled back to linear contexts, and `noDupLay` — no variable
is used twice — is obtained by transporting the heap-side `apart-self`
along `pullTerm`, *not* by reproving `Context.noDupUse`.

---

## 4. Proved vs asserted

### Proved (machine-checked, named)

- **Positive codegen result.** `layPres` at `nilop` and `appop`;
  `layRefl` at both. Plus `refl` witnesses in `Codegen.agda` (lines
  ~408–453) showing that at `twoVar` the disjointness component reduces
  to a nest of `tt`, and that `layRefl` inverts `layPres` on the nose.
- **Negative codegen result.** `noPackPres : SplitPresAt packMap appop →
  ⊥`. The compacting layout (`compact`, dropping dead positions and
  addressing live ones consecutively from 0 — what a real allocator does)
  fails split preservation: at the two-variable application `twoVar` both
  premises compact to `single 0 v1`, so `SplitPresAt` would hand over
  `single 0 v1 # single 0 v1`, refuted by `H.#-self`.

  **The criterion this yields**, in the header's words:

  > a linear source language buys no-aliasing for free precisely when the
  > ALLOCATOR IS INJECTIVE ON VARIABLES, uniformly in the context.

  Compaction is injective on each usage *separately* but not stably
  across a split. That is the whole difference. Note what the pair of
  results does and does not establish: split preservation is a genuine
  constraint that some plausible layouts fail — **not** that identity
  layout is the only one that works, and **not** any statement about
  layouts other than `layout` and `pack`.
- **DCE is vacuous linearly.** `deadBinder : DeadBinder ⊢ ⊥G`, via
  `budgetEq` (`occ ≡ live + lam`, produced as the *motive* of the fold, the
  Quicksort idiom). Consequence: `dceUnique` — any two DCE passes agree,
  so the pass is the identity. Hypothesis is only that the occurrence
  *profiles* agree, which is weaker than syntactic equality.
- **β is safe, and is evaluation.** `substUP` is an `Iso`; `substIsApp`
  holds by `refl`. One direction of the iso is definitional, the other
  costs exactly one `boolΠ`-η (the documented "arities have no η" trap).
- **`foldRollPass : foldTm TmG roll ≡ idPass`** — the untyped
  `Passes/Framework.agda` asserts the corresponding fact about `idAlg`
  without proving it.
- **Elaboration fails exactly at the binder.** `¬presLam`, `¬reflLam`;
  `presVar`/`presApp`/`reflVar`/`reflApp` positive. Contrast
  `Passes/Inline.¬subSplitPres`, which fails at `varOp`. In each case the
  obstruction is the operation the pass rewrites.
- **The checker computes and refutes.** `Tests.agda` — `decisions`,
  `sizes` are single `refl`s; `no-dup`, `no-drop` are internal
  refutations `Lin m → ⊥*` obtained via `refute`, with `no-drop`
  specifically separating linear from affine.

### Asserted, or explicitly disclaimed

`Opt.agda`'s closing section "WHAT THE INDEX BOUGHT" is the honest
ledger; it is worth reading in place. Its "BOUGHT NOTHING" column:

- **Semantic correctness.** `TmG ⊢ TmG` says nothing about meaning.
  `etaPass` could return `λx. x` for every input and still typecheck.
  Every claim of the form "this really is η" in `Opt.agda` §5 is a claim
  about the code, not a theorem. Fixing it needs an evaluation relation
  carried in the motive (the Quicksort `Spec` move); the file does not do
  it.
- **Termination of a normaliser.** `linGrading` grades by `live`, which
  *increases* under a binder, so `hyloC`/`löb` are unavailable and the
  passes are single-sweep **by necessity, not by choice**. (`foldTm`'s
  structural recursion on `Tm` is therefore a genuine phase-1 primitive,
  and marked as one.)
- **Confluence, or any relation between the passes.** That `betaPass then
  etaPass` beats either alone is an empirical remark about the `refl`
  tests in §6.
- **The index algebra is not free.** `Opt.agda` §1 is ~150 lines of
  `Use⊎` combinatorics (associativity, exchange, markers) that an
  unindexed development does not have. Paid once, reused by every pass,
  but a real cost. "What the framework gave was the SHAPE (`⊗ˢ` is the
  splitting) rather than the proofs."
- **The negative side of the checker is ordinary syntax.** `Check.agda`
  §"WHERE THE FRAMEWORK DOES NOT REACH" (2): `linUniq` is proved by
  ordinary induction on two linear terms; the framework shortened none of
  it. Positive rules are free (`linApp` inspects neither subterm), the
  refutation branches are not.
- **`join?` is a metalanguage `⊎`, not an internal `Dec⟨_⟩`, and has to
  be** — `Check.agda` §"WHERE THE FRAMEWORK DOES NOT REACH" (1). `Use⊎`
  lives over `monoidSig`, everything else in that file lives over `λSig`,
  and `CarrierMap.Reindex` relates promodels over **one** signature. So
  the two theories can currently only meet in the metalanguage. This is
  the pipeline's one structural seam.

---

## 5. `Instances/Affine/` — a fork, not a stage

`Instances/Affine/{Base,Syntax,Dead,Contrast}.agda` is a **second
instance at Phase 2**, not a step in the chain. It re-presents the usage
promodel with one constructor restored:

```
adrop : Aff⊎ u v w → Aff⊎ (false ∷ u) (false ∷ v) (true ∷ w)
```

— a live resource claimed by neither premise, i.e. weakening; the header
reads it as the ownership discipline of a Rust fragment. `Affine/Base.agda`
deliberately does **not** import `LinLam`, copying `Usage` verbatim so
that nothing load-bearing depends on a file another agent may be editing;
all cross-references are quarantined in `Contrast.agda`.

Its function in this document is as a **boundary marker**: it says which
Phase-2 and Phase-3 theorems depend on linearity and which merely depend
on having a promodel. The table in `Affine/Base.agda`'s header is the
authoritative version; abbreviated:

| | linear (`LinLam`) | affine (`Affine`) | cartesian (`Affine/Base` §last) |
|---|---|---|---|
| contraction | refuted, `Context.noDupUse` | refuted, `noDupAff`; sharper `affDiag` | holds, `cdiag` |
| weakening | refuted, `Contrast.noWkLin` | holds, `wkUnit`, `affWk` | holds (a fortiori; not separately proved) |
| dead code | **vacuous**, `Opt.deadBinder` | **real**, `Dead.deadWitness`, `Dead.noDeadEmpty`, `Dead.dceNotUnique` | real (not separately proved) |
| grading (`deg<`) | holds, `Context.liveSplit` (an *equation*) | holds, `liveSplit≤` (an *inequality*) | **refuted**, `cartNoProper` — for *every* grading |
| budget | `occ ≡ live + lam`, `Opt.budgetEq` | `occ ≤ …`, `Dead.budgetLe`; `≥` half refuted by `Dead.noBudgetGe` | not done |

Two results are worth extracting because they bear directly on the
pipeline:

- **Grading survives affinity.** Losing resources is fine for a
  well-founded recursion; only *gaining* them is a problem. So
  `Ind`/`Guard`/`hyloC` remain available verbatim — but see
  `cartNoProper`: no grading whatsoever works cartesianly, because the
  diagonal `Cart⊎ u u u` makes a slot equal to the whole.
- **Phase 3's headline theorem is exactly what affinity costs.** The
  linear DCE proof uses the `≥` half of the budget at the λ-body, and
  `adrop`/`tdrop` is the sole source of its failure —
  `Dead.deadBinderFromGe` takes the missing step as an explicit premise,
  so the linear theorem returns verbatim the moment it is available.
  Affinely the conclusion is not merely unproved but **false**
  (`noDeadEmpty`), and the optimiser acquires real content
  (`dceNotUnique`) and with it a correctness obligation the index does
  not supply.

`Contrast.agda` is the only file in the directory that mentions `LinLam`:
`lin→aff`, `lin⊊aff`, `linTm→aff`, `noWkLin`, `linDeadVacuous`,
`linDceUnique`, `noLinearK`.

**There is no affine `Codegen`.** Whether `layPres` survives `adrop` is
not addressed anywhere in the tree.

---

## 6. Open questions and gaps

Each item is sourced. Nothing here is invented.

1. **`Reindex` along a map of signatures.** `Check.agda` marks this
   `BELONGS UPSTREAM`: a functor on operations/arities plus a carrier map
   over the induced sort map. With it, `join?` would be the image of the
   linear theory's own decision for `Split appop`
   (`Decidable.Splittings`) and `Check.agda` would contain no
   metalanguage `⊎`. Without it the de Bruijn and linear-context theories
   meet only in the metalanguage. This is the single largest structural
   gap in the pipeline.
2. **`⊸ᶠ` / `Focus linFib appop true` belongs in `Context.agda`.**
   `Opt.agda` §3.4 builds it locally only because that file may not touch
   `Context.agda`. The header calls the move "a one-line change to
   `Context.agda` and a deletion here"; `Refinement` and `CanonicalFocus`
   would both want it.
3. **No normaliser.** See §4 — the framework grading is the wrong
   measure, so the passes are single-sweep.
4. **No semantic statement about any Phase-3 pass.** `Opt.agda` §5's
   comments name what each branch is *for*; nothing checks it.
5. **No affine codegen; no cartesian budget row.** Neither is attempted.
6. **The `Codegen` asymmetry is an artifact, and says so.** `uright`
   needs `#-cons-r` while `uleft` does not, because `_#_` recurses on its
   left argument. Header: "an artifact ... not a mathematical fact." Not
   a gap, recorded so nobody hunts for meaning in it.
7. **`Affine/Base.agda`'s header table cites `cdup`, which is not
   defined.** `grep -rn cdup src/` matches only that header line;
   `cdiag` and the constructor `cboth` do exist. A dangling citation, not
   a broken proof.
8. **Both directories are untracked.** Nothing in `LinLam/` or `Affine/`
   is committed on `theory-generic-lambekd`.

Not verified by this document, and needing a build to settle: whether
each file currently typechecks. The reading above is a source reading
only. (Absence of holes and postulates was checked mechanically; that is
weaker than a green build.)

---

## 7. Related documents

These exist and are cited rather than duplicated. **None of them mentions
`LinLam`, `Codegen`, or `Affine`** (checked by grep), so none of them is
a substitute for this file.

- `AUDIT.md` — read-only audit of `Instances/{Strings,Bags,Lambda}` for
  duplication and phase-boundary leaks. Headline: `Strings` is in good
  shape, `Bags` is not.
- `FINDINGS.md` — "What this DSL buys, measured." The two-sided result
  about where the abstraction pays. Concerns the *untyped* `Lambda`
  development (mode checkers, `Readable.agda`, `Modes/`), i.e. the
  contrast case the LinLam headers keep citing.
- `PORTING.md` — file-by-file cost of making `Grammar/` generic in the
  theory (57 of 157 files mention `⊗`).
- `CONVENTIONS.md` — house rules learned the hard way; in particular
  `Eq` vs cubical `transp`, which is why `Use⊎`-adjacent equations are
  stated at `Eq.≡`.
- `CLAUDE.md` (repo root) — the phase *discipline*. See §0 above; it is
  not this numbering.
