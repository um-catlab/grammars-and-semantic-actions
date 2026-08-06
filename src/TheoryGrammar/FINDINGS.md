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

## 10. Open

- `Decidable/Splittings.agda:30` `DecSplittings` is the right shape — the *conclusion* of
  `dec-⊗` as an interface, with unique readability and enumerability as two routes into it.
  Deriving the slot↔whole elimination through the residual instead would remove the last
  sanctioned case split, but `Canon.Residual` needs `restJ`, which appears to require the
  slot's complement to be a singleton.
- The `CONJECTURE` in `CanonicalFocus.agda`.
- `Inductive.agda` exports only a non-dependent `fold`; the dependent eliminator `indμ` is
  stranded in `Instances/Lambda/Initial.agda`.
