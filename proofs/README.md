# The grounding gate — proved correct

A verification gate accepts a proof as *grounded* only if the proof **physically rebuilds
and its source hash still matches the live file** — never on a status label. This is a
small Lean 4 model of that gate, with machine-checked proofs that it is **sound**,
**decidable**, and **non-vacuous** (it provably *refuses* bad input, not merely accepts
good input).

It is the buildable half of a two-part artifact: a runnable checker (`pap_check`) plus
this — *the honesty machinery proving its own correctness.* You don't have to take the
checker's word for what it does; the rule it enforces is stated and proved here.

## Build it (≈ seconds, nothing but a Lean toolchain)

```sh
lake build          # type-checks GateProofs.lean; exits 0
```

No Mathlib. No `native_decide`. Plain Lean 4. Every theorem is reduced by the Lean kernel.

## Audit the trust base yourself

```sh
lake env lean AxiomAudit.lean   # prints the exact kernel axioms each theorem depends on
```

Output: the soundness/refusal theorems rest on a single standard axiom (`propext`); the
non-vacuity theorems (`gate_discriminates`, `not_rubber_stamp`, `not_black_hole`) rest on
**none**. There is no `Lean.ofReduceBool` (i.e. no
`native_decide`), no `Classical.choice`, no `sorry`/`admit`/`axiom` in the file.

## What is proved (`GateProofs.lean`)

| Theorem | Claim |
|---|---|
| `sound` | If the gate accepts, then the witness was GROUNDED **and** the build was executed **and** it exited 0 **and** the recorded hash matched live. Grounding is earned, never asserted from a label. |
| `stale_refused` | Any receipt whose recorded hash ≠ the live hash is refused ("the source changed since the build"). |
| `divergent_refused` / `noncompile_refused` / `unexecuted_refused` | A non-GROUNDED witness / a non-zero build exit / an unexecuted build is always refused. |
| `gate_discriminates` | The gate accepts a good receipt **and** refuses one instance of each failure mode (the closest-failing inputs — `goodReceipt` with a single field perturbed). |
| `not_rubber_stamp` / `not_black_hole` | The gate is neither constant-accept nor constant-refuse. |

`gate_discriminates`, `not_rubber_stamp`, `not_black_hole` are the **non-vacuity** core:
a gate that accepted everything would satisfy "soundness" vacuously — these rule that out.
(`gate_discriminates`, `not_rubber_stamp`, and `not_black_hole` are the kernel-checked non-vacuity guarantees.)

## What this does *not* claim (the boundary, stated first)

- It models the **acceptance rule** of the checker's grounding branch — it is **not** a
  verification of the full implementation, and not a model of the coherence checks.
- A *grounded* result means the cited source built and still matches — **not that the
  claim is true about the physical world.** Coherence + freshness is not semantic
  correctness. (A result can be coherent, grounded, and still wrong about reality.)
