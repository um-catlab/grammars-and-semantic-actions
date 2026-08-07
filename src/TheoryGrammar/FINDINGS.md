# What this DSL buys, measured

Results from building, on `TheoryGrammar`: scope checking, four substructural mode
checkers, a bidirectional typechecker, and an optimization-pass suite. Every claim
below points at a theorem in the tree; nothing here is prose-only. Around 130 `refl`
tests across four suites, each checked non-vacuous by perturbation (flip an expected
value, confirm Agda rejects it, restore).

The point of the exercise was not the programs. It was to find out where the calculus
does the work and where it only relabels it.

---

## 1. Where the abstraction pays, and where it doesn't

This is the headline, and it is a two-sided result.

**It pays** when the substrate is *uniquely readable*. In `Instances/Lambda/Readable.agda`,
routing the slot decisions through `Precise`'s `decSlots¹`/`decSlots²` collapsed 16
`with`-clauses into 8 one-liners. The framework absorbed the case analysis.

**It only relabels** when the substrate is a quotient. The same rewiring applied to
`Modes/{Concat,Interleave,Overlap}` made the files *longer* — 107→126, 112→126, 136→152.
What went away was ~44 `inl`/`inr` occurrences and 3 imports; the case split moved into a
sanctioned eliminator rather than disappearing. `decSlots¹/²` do not apply there at all,
because they live in `Precise`, parameterised by `splitProp`, and

- `Modes/Laws.agda:149` `splitNotProp` — **`Split` is not a proposition** for a resource
  substrate. A one-name context splits two ways.

Refuting one cut refutes nothing when there are |Γ|+1 of them. That is the whole
difference.

---

## 2. Four substructural modes from one term

`Modes/Core.agda` defines, once:

```agda
Uses (var n)   =  Lf n                  -- leaf, possibly modal
Uses (app u v) =  Uses u ⊗ᶜ Uses v      -- the context tensor
Uses (lam n t) =  Uses t ⟜ᶜ ⌈ n ⌉       -- ITS residual
```

Ordered, linear and relevant are that same term at three context substrates — concatenation,
interleaving, and interleaving plus one constructor. `var`/`app`/`lam` never move.

**Exchange and contraction live in `Split`. Weakening does not.** Contraction is one extra
constructor (`both`) on the interleaving relation, because contraction happens *at a split
node*. An unused variable never reaches a split — in `λx.λy.x` there is no application at
which to discard `y` — so affine cannot be a splitting discipline. It is a *leaf modality*,
`Lf n = ⌈n⌉ ⊗ ⊤`.

Confirmed independently from the pass side: `A ⊗ B ⊢ A` is not a term at all, since `⊢`
preserves the index and a projection does not. And in the existential form
(`Passes/Framework.agda:38`) the discard is invisible — **that form is affine by
construction**, having already forgotten the index.

---

## 3. Passes are not free, and the reason is exact

The tempting analogy — "`_⊢_` preserves the index, so a pass can only rearrange, as
`mergesort` can only permute" — is false.

- `Passes/Framework.agda:38` — `Out Γ = ⊕ᴰ Raw (λ t _ → Scoped Γ t)` is **constant in the
  index**. That is the entire difference from `Sorted ⊗ Sorted ⊢ Sorted`, where the index is
  preserved and does the work.
- `Passes/Rename.agda:158` `nmTr→id` — transport leaves one obligation per *constant* of the
  description, and it forces `ρ n ≡ n`. **The only pass free by transport is the identity.**

What *is* free: the whole additive fragment, definitionally, for any carrier map — including
`pull Dec⟨A⟩ ≡ Dec⟨pull A⟩` by `refl`, so the scope checker transports along inlining at no
cost. The one additive former that does not transport is `⌈ a ⌉`, the only one mentioning
the carrier.

Substitution, localised: it *preserves* splittings at `appOp` and `lamOp` by `Eq.refl`, and
fails only at `varOp` (`Passes/Inline.agda:142` `¬subReflects`).

---

## 4. Bidirectional typing = uniqueness, on the refutation side

`SimplyTyped/Unique.agda:173` states uniqueness of the synthesised type *inside* the
calculus — two synthesis derivations yield the calculus's own `ty`-sorted representable,
proved by the generic `fold`.

`SimplyTyped/Check.agda:209` `dec-at` takes that uniqueness as an **explicit argument**, so
the dependency is checked rather than remarked. It is used in exactly two places, both
refutations. The honest form of the claim: without uniqueness you can decide "some type" but
cannot refute "*this* type".

The third sort cost almost nothing and paid: `Discrete Ty` is never assumed, because types
have operations, so type equality is `dec-⊗` plus the representable iso. `Discrete Name`
still is — names have no operations, so there is no tensor to decide. That contrast is the
cleanest thing many-sortedness bought.

---

## 5. `⊤ ≅ μ(shape)`, and what generalises

`Instances/Lambda/Initial.agda:264` — both directions, a real `Iso`. `PORTING.md` lists this
as unbuilt.

It generalises free to any signature with **constant `resultSort`**. Otherwise `⊗e o G :
Functor (resultSort o)` is a stuck neutral for bound `o`, so the generic sum
`⊕e ops (λ o → ⊗e o …)` does not typecheck at any fixed sort; the fix is to ford `⊗e` with
`resultSort o Eq.≡ s` — in `Eq`, not `Path`, so definitional equations survive. That is a
change to `Inductive.agda`, not to instances.

---

## 6. The `unsplit` law — and why it must NOT be a field

`op o (parts o m sp) Eq.≡ m` (`Instances/Lambda/Fibered.agda:86`, `Eq.refl` in every clause)
was demanded four separate times: as the brief's one known soundness gap; by SimplyTyped for
the representable/tensor iso; by Passes, blocking `SplitPresAt` from a `ModelHom`; and
constructively, as what makes a tensor eliminator *derived* rather than primitive
(`Initial.agda`, primitive count 3→2).

Why it is necessary there: `⊗ˢ-E` returns `m`, an abstract `sp`, and payloads at
`parts o m sp a`, so a constructor hypothesis lands at `P (op o (parts o m sp))`, not `P m`.
`parts-split` runs the other direction. There is no third route out of the record.
Transporting along `unsplit` is the only move — and it is what a pattern match was doing
silently.

**But it is refuted for quotient substrates.** `Modes/Laws.agda:143` `no-unsplit` exhibits a
counterexample at the bag substrate: `Ilv (x∷[]) (y∷[]) (y∷x∷[])` holds while `op mul = _++_`
gives `x∷y∷[]`. So adding it as a *field* of the shared record would exclude every resource
substrate. It belongs as a side-car — a module parameter, as `Representable.Repr` already
takes it.

---

## 7. The canonical residual needs no freeness at all

`CanonicalFocus.agda` proves `plug`/`unplug`/β/η/`⊸-UP` generically using **neither
`unsplit`, nor "splittings generated by `split`", nor `Fib .Split`**. `Canon.focus`
manufactures its `SplitAt` from `Assembly` + `op`, so the adjunction is independent of the
substrate's splittings. The file's former freeness caveat was attached to the wrong theorem;
what remains genuinely open is stated as an explicit `CONJECTURE`, one of whose hypotheses is
the refuted `unsplit`.

Enabling lemma: `CanonicalFocus.agda:43` `singJ`, singleton induction in Eq-world, whose
computation rule is definitionally `refl`.

---

## 8. `refl` vs `funExt`: the arity costs, the sorts do not

Uniform cause: `Σ`/`Π`/`Unit`/`Unit*`/`Lift` have definitional η; `Bool` and `Eq._≡_` do not.

| law | cost |
|---|---|
| `⊗ˢ` β/η, `⊸ᶠ` β/η (all foci, incl. cross-sorted) | `refl`, generically |
| `parts-split` at a `Unit` arity | `refl` |
| `parts-split` at a `Bool` arity | `funExt`, `refl` at each slot |
| `var-η` (unary op) | `funExt` over `∀ t` only |
| `Adjunctions.agda:65` `fun-η` (binary op) | `funExt` over `∀ t` **and** over the arity |
| `⟜-η` | `funExt`; provably cannot be `refl` (it equates two functions) |

Nothing in the sort machinery degrades any law. The residual at the binder slot — source and
target at *different* sorts — has exactly the same definitional β/η as the single-sorted ones.

---

## 9. Traps, each of which cost real time

- **`Eq` vs cubical `transp`.** `Eq.J` reduces on `refl`; cubical transport does not, and
  every test here is a `refl` that must evaluate. Bit this codebase three times. `⌈⌉-E`
  matches `Eq.refl`, but a witness built from `Discrete` via `pathToEq` does *not* reduce to
  `Eq.refl` — which is why `DeBruijn.toIx` discards its representable instead of eliminating
  it.
- **Grammar-valued implicits never infer under a term index.** The metavariable's context
  already contains `m`, so `?A m ≡ B m` is not a Miller pattern. Pass grammars explicitly.
- **Extended lambdas are not convertible**, even syntactically identical ones. `⊗ˢ-E` cannot
  be *stated* at a slot family written `λ { true → … ; false → … }`; the family must be a
  named definition. Bites mixed-sort operations only.
- **Sum-matching belongs to the framework, not to instances.** `Decidable/Additive.agda:103`
  `⊕-E-at-factors` proves the pointwise rule is `⊕-E` with the quantifier moved, so nothing
  new is assumed. 26 sites across 10 files route through it.
- **Auditing.** Grep `postulate`/`{!`; every `data` must be a sort, operation, carrier,
  splitting or tag — never a judgment. Grep **both** `with .*dec` and `inl|inr` under
  `Instances/`: the second catches sites the first misses, which is how 26 sites were once
  miscounted as 12.

---

## 10. Partial theories

The `Fibered` / `LaxPoint` split makes partiality expressible: `Fibered` alone (carrier,
`Split`, `parts`) **is** the notion of a partial algebra — `Split o m` says which
decompositions exist, and nothing requires that every tuple composes. Two instances exercise
the two different senses of "partial".

### Partial operations — `Instances/Field/`

- `Instances/Field/NoPoint.agda:49` `noFieldPoint : LaxPoint fldFib → ⊥`. **A theory the
  framework can express that provably admits no total operation.** The obstruction is
  *located*, not merely present: `rngPoint : LaxPoint rngFib` is the same carrier, splittings
  and parts with `invOp` deleted, so the failure is attributable to the partial operation.
- `img-inv≡nonzero : ⊗ˢ invOp ⊤ ⊣⊢ ¬G ⌈ f0 ⌉` — **both directions**. Invertibility *is*
  internal nonzeroness, not merely implies it. `dec-invOp : ⊤G ⊢ Dec⟨ ⊗ˢ invOp ⊤ ⟩` makes the
  domain a genuine internal decision carrying its exclusion.
- **CORRECTION, worth stating loudly.** `⊗ˢ o ⊤` is the **image**, not the domain of
  definition, and the right condition for `⊤G ⊢ ⊗ˢ o ⊤` is **surjectivity, not totality**.
  Counterexample proved: `NoPoint.agda:129` `no-img-zero` — `zeroOp` is a *total* constant
  (it lives in the fragment that has a `LaxPoint`) and its image is still proper. Any total
  constant refutes "image is ⊤ iff total". The real domain of definition lives one sort over,
  as `Domˢ o i` at `sortOf o i`, and *that* one is clean: a `LaxPoint` forces
  `⊤G ⊢ Domˢ o i` at every fillable slot.
- **Nothing in the multiplicative layer breaks under partiality.** `⊗ˢ`, `MultiHomˢ`,
  `curryˢ`/`uncurryˢ`, β/η, `⊸ˢ`, `⊸ᶠ`, `⊗ˢ-map` mention only `Split`/`parts` and applied to
  a partial operation unchanged. What degrades is *inhabitation*: `⊗ˢ invOp A` is empty at
  `f0` for every `A`, so precisely the map the refutation kills is the unavailable one.
  `⊸ᶠ` degrades dually and harmlessly — it quantifies over `SplitAt x`, so it is vacuously
  `⊤` there.

### Partial equations — `Instances/Traces/`

Trace monoids: total operation, *conditional* commutativity. The carrier is not quotiented;
the commutation goes into `Split`, exactly as `Bags` already does.

- **Interpolation, proved as real `Iso`s against the originals** (`Strings.Base` and
  `Bags.Base` are imported and aliased, not restated): `Traces/Ordered.agda:66`
  `ITr ⊥I ≅ Split3`, `Traces/Commutative.agda:61` `ITr ⊤I ≅ Ilv`. **The two existing resource
  substrates are the endpoints of one family.**
- The endpoints fail *differently*. `⊤`/`Ilv` is constructor-for-constructor, the only
  discrepancy a nested `Unit` whose uniqueness is `refl` by η. `⊥`/`Split3` is a genuine shape
  mismatch — `Split3` stops at one `nil` when the left factor runs out, `ITr` must still walk
  the rest by `right`s — packaged as `bump`, which identifies the indices **with no transport**.
  Neither direction needed `Eq.J`, `subst`, or a dimension variable.
- Exhibited numerically: the word `abc` gives **4 < 5 < 8** factorisations under ordered,
  partially commutative, and fully commutative relations.
- **`Uses` from `Modes/Core.agda`, unchanged, instantiated here is a partially commutative
  substructural logic** strictly between ordered and linear. With 0⌣1 independent and 2
  independent of nothing: `λ0.λ1. x1 x0` accepted, `λ0.λ2. x2 x0` rejected. Same term, same
  grammar, one substrate — the independence relation decides.
- Cost of the conditional equation: **nothing downstream of `Split`**. `Fibered`, `LaxPoint`,
  `⊗ˢ`/`⊸ᶠ` β/η, `DecEnumerable`, `DecSplittings` and the whole mode were reused verbatim.
  The costs are localised in the *enumeration*: two side hypotheses on `I` (decidable,
  propositional — Strings needs neither because shape implies them, Bags because they are
  vacuous) and one `subst` on a Path in `Enumeration.pickIn`, which sits entirely on the
  refutation side so nothing reduces through it.

---

## 11. Open

- `Decidable/Splittings.agda:30` `DecSplittings` is the right shape — the *conclusion* of
  `dec-⊗` as an interface, with unique readability and enumerability as two routes into it.
  Deriving the slot↔whole elimination through the residual instead would remove the last
  sanctioned case split, but `Canon.Residual` needs `restJ`, which appears to require the
  slot's complement to be a singleton.
- The `CONJECTURE` in `CanonicalFocus.agda`.
- `Inductive.agda` exports only a non-dependent `fold`; the dependent eliminator `indμ` is
  stranded in `Instances/Lambda/Initial.agda`.
