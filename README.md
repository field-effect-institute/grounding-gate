# A verification gate that catches stale and spoofed grounding

Most "I verified this" claims bottom out in a *status label* — something was marked done.
This gate does better on the one axis it can: it accepts a result as **grounded** only if
the cited source **still hashes to what its build receipt recorded** — a live content check
against the file on disk, not the receipt's say-so. So a stale, drifted, or spoofed receipt
is caught. It *trusts* the receipt's reported build-exit and verdict; actually re-running
the build at check time is a future rung, not a claim here. You can watch it refuse
spoofed, stale, and overclaimed inputs.

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
| `01_ACCEPT_grounded` | **COHERENT ✓** | the cited source still hashes to what the receipt recorded — freshness holds, grounding earned |
| `02_REJECT_spoofed_grounding` | **INCOHERENT ✗** (WF6) | labeled `grounded` but no resolvable receipt — a status label alone never earns grounding |
| `03_REJECT_stale_receipt` | **INCOHERENT ✗** (WF6) | the live source no longer hashes to the receipt's recorded hash — "the proof changed since the build" |
| `04_REJECT_license_overclaim` | **INCOHERENT ✗** (WF5) | claims an *empirical* result but cites only a Lean proof — a proof can't license a world-measurement |

The honest demonstration is that **it says NO** — to a spoofed receipt, a stale (hash-drifted)
receipt, and a prose overclaim. (It does not test a non-compiling build — that case lives in
the Lean model, `noncompile_refused`, not in this demo.)

## Build and audit the proofs yourself

```sh
cd proofs
lake build                       # type-checks GateProofs.lean — exits 0, no Mathlib needed
lake env lean AxiomAudit.lean    # prints the exact kernel axioms each theorem rests on
```

The soundness/refusal theorems rest on one standard axiom (`propext`); the non-vacuity
theorems rest on none. No `native_decide`, no `sorry`/`admit`/`axiom`. See `proofs/README.md`.

## What this is — and is NOT (stated up front)

- It checks **coherence** (a claim's trust gradient holds up) and **grounding-freshness**
  (the cited source still hashes to what the receipt recorded — catching drift, staleness,
  and spoofed receipts). It **trusts** the receipt's reported build-exit/executed/verdict —
  it does **not** re-execute the build at check time (a future rung). And it does **not**
  check that a claim is **true about the physical world** — a result can be coherent,
  grounded, and still wrong about reality.
- `proofs/` models the gate's *acceptance rule* and proves it correct; it is not a
  line-by-line verification of the Python implementation.
- `proof_index_subset.json` is a small **slice-local** register holding only the gate's own
  proofs — not a larger library. This repo is exactly what it says it is: a gate, its
  proof, and four worked judgments.
