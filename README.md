# A verification gate that refuses its own author's overclaims

Most "I verified this" claims bottom out in a *status label* — something was marked done.
This is a small, runnable gate that accepts a result as **grounded** only if the cited
proof **physically rebuilds and its source hash still matches the live file** — never on a
label. It refuses spoofed, stale, and overclaimed inputs, and you can watch it do so.

Two parts, both reproducible from a clean clone:

```
verifier/   pap_check.py — the gate (coherence + grounding checks). Pure Python 3 stdlib.
proofs/     GateProofs.lean — the gate's rule, modeled and PROVED correct in Lean 4
            (sound, decidable, non-vacuous). Plain Lean, no Mathlib, no native_decide.
examples/   four expressions the gate judges — one accepted, three refused.
```

## Watch it work (≈ 1 minute)

```sh
./run_demo.sh
```

| Example | The gate says | Why |
|---|---|---|
| `01_ACCEPT_grounded` | **COHERENT ✓** | the cited Lean proof builds and its hash matches the receipt — grounding earned |
| `02_REJECT_spoofed_grounding` | **INCOHERENT ✗** (WF6) | labeled `grounded` but no real receipt — a status label never earns grounding |
| `03_REJECT_stale_receipt` | **INCOHERENT ✗** (WF6) | the receipt's hash has drifted from the live source — "the proof changed since the build" |
| `04_REJECT_license_overclaim` | **INCOHERENT ✗** (WF5) | claims an *empirical* result but cites only a Lean proof — a proof can't license a world-measurement |

The honest demonstration is that **it says NO** — to inputs designed to fool it, including
ones that merely *assert* they are grounded.

## Build and audit the proofs yourself

```sh
cd proofs
lake build                       # type-checks GateProofs.lean — exits 0, no Mathlib needed
lake env lean AxiomAudit.lean    # prints the exact kernel axioms each theorem rests on
```

The soundness/refusal theorems rest on one standard axiom (`propext`); the non-vacuity
theorems rest on none. No `native_decide`, no `sorry`/`admit`/`axiom`. See
`proofs/README.md` and `proofs/negative_control_verdict.yaml` (verdict: `NON_VACUOUS`).

## What this is — and is NOT (stated up front)

- It checks **coherence** (a claim's trust gradient holds up) and **grounding-freshness**
  (a cited proof really builds and still matches). It does **not** check that a claim is
  **true about the physical world** — a result can be coherent, grounded, and still wrong
  about reality. Semantic correctness is a separate, harder problem and is not claimed here.
- `proofs/` models the gate's *acceptance rule* and proves it correct; it is not a
  line-by-line verification of the Python implementation.
- `proof_index_subset.json` is a small **slice-local** register holding only the gate's own
  proofs — not a larger library. This repo is exactly what it says it is: a gate, its
  proof, and four worked judgments.
