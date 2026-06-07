# The grounding gate — proved correct

This is a small Lean 4 model of a grounding gate, with machine-checked proofs that it is
**sound**, **decidable**, and **non-vacuous** (it provably *refuses* bad input, not merely
accepts good input). The modeled gate accepts a result as *grounded* only when the receipt
records a GROUNDED, executed, exit-0 build **and** the cited source still hashes to what the
receipt recorded — the last being a live content check against the file, which is what
catches a stale or spoofed receipt. (The first three are the receipt's recorded fields; the
gate trusts them.)

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
| `sound` | If the gate accepts, then the receipt recorded a GROUNDED, executed, exit-0 build **and** its recorded hash matched the live source. (The hash match is the one check made against the live file; the other three are the receipt's recorded fields.) |
| `stale_refused` | Any receipt whose recorded hash ≠ the live hash is refused ("the source changed since the build"). |
| `divergent_refused` / `noncompile_refused` / `unexecuted_refused` | A receipt that *records* a non-GROUNDED verdict / a non-zero build exit / not-executed is always refused. |
| `gate_discriminates` | The gate accepts a good receipt **and** refuses one instance of each failure mode (the closest-failing inputs — `goodReceipt` with a single field perturbed). |
| `not_rubber_stamp` / `not_black_hole` | The gate is neither constant-accept nor constant-refuse. |

`gate_discriminates`, `not_rubber_stamp`, `not_black_hole` are the **non-vacuity** core:
a gate that accepted everything would satisfy "soundness" vacuously — these rule that out.

## What this does *not* claim (the boundary, stated first)

- It models the **acceptance rule** of the checker's grounding branch — it is **not** a
  verification of the full implementation, and not a model of the coherence checks.
- The rule **trusts** the receipt's `verdict`/`executed`/`buildExit` fields and independently
  checks only the source-hash freshness (`recordedSha = liveSha`). Re-executing the cited
  build at check time — which would let it verify those three too — is a real next step, not
  a current property.
- A *grounded* result means the receipt's recorded build looked good **and** the cited source
  still hashes to what it recorded — **not** that the claim is true about the physical world.
  Coherence + freshness is not semantic correctness.
