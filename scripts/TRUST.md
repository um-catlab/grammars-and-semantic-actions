# What is actually verified about the executable

Short version: **one link in the chain is proved, and it is not the link
most people mean when they say "verified compiler".** This file says
exactly where the proof stops.

## The chain of custody

```
  Tm u                      a linear lambda term
    │
    │  compileU / compileTm
    ▼
  Program = List LI         an Agda datatype
    │
    ├──────────── PROVED ─────────────────────────────────────────┐
    │   Codegen.runU : exec (compileU u) [] Eq.≡ layout u          │
    │   Machine.exec-sound : Dets p → sem p h (exec p h)           │
    │   (derived from a Hoare triple via `observe`, not            │
    │    computed-and-compared)                                    │
    └──────────────────────────────────────────────────────────────┘
    │
    │  emitARM                            ◄── NO THEOREM (gap A)
    ▼
  String
    │
    │  scripts/verified-arm64.sh          mechanical extraction, no retyping
    ▼
  gap.s
    │
    │  clang + ld                         ◄── TRUSTED (gap D)
    ▼
  Mach-O arm64 executable
    │
    │  macOS loader + Apple Silicon       ◄── TRUSTED (gap D)
    ▼
  exit status
```

## The one theorem, stated exactly

```agda
runU : (u : Usage) → exec (compileU u) [] Eq.≡ layout u
```

Read it carefully. `exec` is **an Agda function** modelling a **toy
machine** whose instructions are `nopI`, `putI`, `newI`. `layout u` is
the specification. So the theorem says:

> the instruction list the compiler produces, run **under our own model
> of our own toy machine**, yields exactly the specified heap.

It says nothing about ARM, about clang, or about your laptop.

## The gaps, worst first

### (B) AArch64 has no semantics in Agda — the biggest gap

Nothing in the development knows what `str w9, [sp, #16]` does. The step
from `putI 2 v1` to `mov w9,#1 ; str w9,[sp,#16]` is **unmodelled**, so
there is no statement — true or false — connecting the emitted assembly
to `exec`. The exit status matching `live u` is *evidence* the two agree.
It is not a proof.

This is closable, and the pieces exist: `ISA/RiscV/Base.agda` already
models a real ISA as an `ISA.Machine` instance with its own `exec`,
`stepAx`, `progAx` and `refl`-evaluating programs. Doing the same for the
AArch64 subset, then proving the emitter split-preserving, would reduce
this to gap (A) alone.

### (C) The observable is weak, and the compiler is provably blind

The exit status is `live u` — a fact about the **usage**, not about the
**computation**. Worse, this is not an accident of the observable:
`Compile/Semantics/Simulation.agda`'s `noBlindBackend` proves that
`compileU : Usage → Program` factors through the index and *cannot* see
the term. Two different terms compile to the same program:

```agda
_ : compileTm [] idLin  .fst ≡ []
_ : compileTm [] selfApp .fst ≡ []
```

So the executable measures the context layout. It does not evaluate a
lambda term, and no amount of work on this backend will make it do so —
the value-level square is *false* here, not merely unproved. The
term-directed backend (`Compile/LinToRust/Codegen`) is the one where that
square is provable.

### (A) The printer is unverified

`emitARM : Program → String` carries no theorem. A bug in `tokS`, `slot`,
`storeToks` or `loadToks` yields wrong assembly from a right program. The
`refl` tests pin the output **at the terms tested** — that is testing,
not proof. Closing it means either an AArch64 parser plus a round-trip
lemma, or gap (B)'s route.

### (D) Trusted base outside Agda

clang's assembler, the Mach-O linker, the macOS loader, the silicon.
Standard for any verified compiler that emits text (CompCert has the same
boundary), but it is in the trusted base and should be named.

### (E) Trusted base inside Agda

The Agda typechecker; `--lossy-unification` (on in every file here); the
Cubical library. No `postulate` and no `{-# TERMINATING #-}` anywhere in
this pipeline — that much was checked.

### (F) Model limits that would bite silently

`Val` has three elements. `Loc` is unary `ℕ`. The emitted frame is a
fixed 256 bytes, i.e. 32 slots, and **nothing checks that addresses stay
below 32** — a larger usage would emit out-of-frame stores and the script
would happily assemble them.

## What you may and may not say

**May say.** "The instruction list is proved to produce the specified
heap under a formal machine model, and the assembly printed from it runs
on real hardware and agrees with the prediction at the cases tested."

**May not say.** "Verified ARM64 compiler." "The executable is proved
correct." "The binary is verified." None of those are supported: the
target ISA is unmodelled, the printer is unproved, and the compiler is
provably blind to the term it is compiling.

## The honest one-liner

This is a **prototype demonstrating the shape of a verified pipeline**,
with one genuinely proved link and a clearly marked boundary — not a
verified compiler in the CompCert sense. The interesting content is
upstream of the assembly: the resource discipline (`layPres`, no-aliasing
from a missing constructor), the impossibility results (`noBlindBackend`,
`noRegAllocPres`), and the three-backend agreement in
`Compile/Showcase.agda`.
