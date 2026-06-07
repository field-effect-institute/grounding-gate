/-
  GateProofs.lean — the PAP grounding gate, modeled and proved correct.

  WHAT THIS IS
  ------------
  A small, self-contained Lean 4 model of the rule the PAP checker (`pap_check.py`)
  enforces when it decides whether a claim has earned the label `grounded`. The
  theorems below prove that rule is:

    • SOUND        — the gate accepts ONLY when the receipt records a GROUNDED, executed,
                     exit-0 build AND the recorded source hash still matches the live file
                     (the one condition checked against the file on disk). A receipt whose
                     hash has drifted — the source changed since the build — is refused.
    • DECIDABLE    — "is this receipt fresh / accepted?" is a total, computable question.
    • NON-VACUOUS  — the gate genuinely DISCRIMINATES: it accepts at least one receipt and
                     refuses at least one of EACH failure mode. A gate that accepted
                     everything (or nothing) would satisfy "soundness" vacuously; the
                     non-vacuity theorems rule that out.

  TRUST BASE (stated so a reviewer can audit it exactly)
  ------------------------------------------------------
  Plain Lean 4. No Mathlib. No `native_decide`. Every proof is `simp`/`decide`/`rfl`
  reduced by the Lean kernel. The whole file builds with only a Lean toolchain.

  WHAT THIS DOES *NOT* CLAIM (the abstraction boundary — honesty first)
  --------------------------------------------------------------------
  This models the CORE of `pap_check.py`'s WF6 grounding-acceptance branch (mechanism
  `lake_build`): the four conditions a computational grounding receipt must meet. It is a
  faithful model of that RULE — not a verification of the Python implementation, and not
  a model of WF1–WF5 coherency, the social-adoption mechanism, or the file parsing. The
  rule TRUSTS the receipt's `verdict`/`executed`/`buildExit` fields; the SINGLE condition it
  checks against the live world is the source-hash match (`recordedSha = liveSha`) —
  re-executing the cited build at check time is a separate, future capability, not modeled
  here. It proves: the grounding rule, as modeled, cannot be fooled into accepting a stale,
  unexecuted, non-compiling, or non-GROUNDED receipt — and that it still accepts a good
  one. Crucially, it does NOT claim a grounded result is TRUE about the physical world:
  coherence + receipt-freshness is not semantic correctness.
-/

namespace PAPGate

/-- A source content hash. In the checker this is a SHA-256 of the cited Lean file; here
    it is an opaque identifier whose only relevant operation is equality. -/
abbrev Hash := Nat

/-- The verdict a grounding witness can return:
    `GROUNDED | DIVERGENT | UNVERIFIABLE`. -/
inductive Verdict where
  | grounded
  | divergent
  | unverifiable
deriving DecidableEq, Repr

/-- A grounding receipt: the recorded claim that a cited Lean source was built.
    `recordedSha` is the source hash AT BUILD TIME (provenance). The LIVE hash is supplied
    by the world at check time (it is `sha256(current file)`), so a receipt cannot fake
    its own freshness from the inside. -/
structure Receipt where
  verdict     : Verdict
  executed    : Bool      -- was the build actually run? (claimed-but-not-run is refused)
  buildExit   : Nat       -- the build's exit code; 0 = success
  recordedSha : Hash      -- source hash recorded when the build was witnessed
deriving DecidableEq, Repr

/-- THE GATE. Mirrors `pap_check.py` `wf6_grounding` (computational branch): a receipt
    earns `grounded` against the live source iff it RECORDS the witness as GROUNDED, the
    build as executed, the exit as 0, AND the recorded hash equals the live hash. Only the
    last is checked against the live file; the first three are the receipt's recorded fields. -/
def accepts (r : Receipt) (liveSha : Hash) : Bool :=
  decide (r.verdict = Verdict.grounded) && r.executed &&
  decide (r.buildExit = 0) && decide (r.recordedSha = liveSha)

/-- The grounding predicate "the gate accepts" is DECIDABLE (it is a `Bool` test). -/
instance (r : Receipt) (live : Hash) : Decidable (accepts r live = true) := inferInstance

/-! ### Soundness — acceptance implies every condition held -/

/-- SOUNDNESS. If the gate accepts, then EVERY condition held: the witness was GROUNDED,
    the build was executed and exited 0, and the recorded hash matched the live source.
    The gate never accepts on a status label alone — grounding is EARNED, not asserted. -/
theorem sound (r : Receipt) (live : Hash) (h : accepts r live = true) :
    r.verdict = Verdict.grounded ∧ r.executed = true ∧ r.buildExit = 0 ∧ r.recordedSha = live := by
  unfold accepts at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ### Each failure mode is refused — universally, not just on the examples -/

/-- STALENESS ⇒ REFUSAL. If the recorded hash differs from the live hash (the source
    changed since the build), the gate refuses — regardless of how good the rest of the
    receipt looks. This is the "the .lean changed; re-witness" guarantee. -/
theorem stale_refused (r : Receipt) (live : Hash) (h : r.recordedSha ≠ live) :
    accepts r live = false := by
  unfold accepts
  simp only [decide_eq_false_iff_not.mpr h, Bool.and_false]

/-- A non-GROUNDED witness never earns grounding. -/
theorem divergent_refused (r : Receipt) (live : Hash) (h : r.verdict ≠ Verdict.grounded) :
    accepts r live = false := by
  unfold accepts
  simp only [decide_eq_false_iff_not.mpr h, Bool.false_and]

/-- A build that did not exit 0 is refused (a non-compiling build cannot ground). -/
theorem noncompile_refused (r : Receipt) (live : Hash) (h : r.buildExit ≠ 0) :
    accepts r live = false := by
  unfold accepts
  simp only [decide_eq_false_iff_not.mpr h, Bool.and_false, Bool.false_and]

/-- A receipt that was never actually executed is refused (no claimed-but-not-run grounding). -/
theorem unexecuted_refused (r : Receipt) (live : Hash) (h : r.executed = false) :
    accepts r live = false := by
  unfold accepts
  simp only [h, Bool.and_false, Bool.false_and]

/-! ### Non-vacuity — concrete negative controls (the load-bearing part)

    A sound gate that ACCEPTED NOTHING would be useless and would pass "soundness"
    vacuously. These closed-term theorems prove the gate is not a black hole and not a
    rubber stamp: it accepts a good receipt and refuses one instance of each failure mode.
    All proved by `decide` (kernel-reduced over `Nat`/`Bool` — no `native_decide`). -/

def liveSha : Hash := 1000

/-- A well-formed grounding receipt: GROUNDED, executed, exit 0, hash matches live. -/
def goodReceipt : Receipt :=
  { verdict := Verdict.grounded, executed := true, buildExit := 0, recordedSha := liveSha }

/-- Negative control — the source changed since the build (hash drift). -/
def staleReceipt : Receipt := { goodReceipt with recordedSha := 999 }

/-- Negative control — the witness did not return GROUNDED. -/
def divergentReceipt : Receipt := { goodReceipt with verdict := Verdict.divergent }

/-- Negative control — the build did not exit 0. -/
def noncompileReceipt : Receipt := { goodReceipt with buildExit := 1 }

/-- Negative control — claimed, but never actually run. -/
def unexecutedReceipt : Receipt := { goodReceipt with executed := false }

/-- NON-VACUITY. The gate accepts a good receipt AND refuses one instance of every failure
    mode. (If you delete any guard from `accepts`, the matching line below fails to build —
    so this theorem also pins the gate's discrimination to the source.) -/
theorem gate_discriminates :
    accepts goodReceipt       liveSha = true  ∧
    accepts staleReceipt      liveSha = false ∧
    accepts divergentReceipt  liveSha = false ∧
    accepts noncompileReceipt liveSha = false ∧
    accepts unexecutedReceipt liveSha = false := by
  decide

/-- The gate is not constant-accept: some input is refused. -/
theorem not_rubber_stamp : ∃ r live, accepts r live = false :=
  ⟨staleReceipt, liveSha, by decide⟩

/-- The gate is not constant-refuse: some input is accepted. -/
theorem not_black_hole : ∃ r live, accepts r live = true :=
  ⟨goodReceipt, liveSha, by decide⟩

end PAPGate
