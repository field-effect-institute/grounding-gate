#!/usr/bin/env python3
"""
The grounding gate — a runnable checker for the well-formedness rules (WF1-WF6).

This is what turns the document format into a language: it can REJECT a malformed
expression and say which rule it broke.

Passes (see pap_ast_v0.1.schema.json $comment for the canonical statements):
  WF1 resolve            every cell.proof_ref resolves (structural: present unless
                         UNTESTED; membership: advisory against the proof register)
  WF2 negative           refuse any NEGATIVE-trust cell
  WF3 frame/no-primacy   every frame_bound expr names a frame; no GLOBAL primacy
                         (a `primary` claim requires a frame)
  WF4 acyclic/open-mouth the compose/via graph is acyclic OR every cycle passes
                         through a receipt-bearing (grounding) node
  WF5 license            prose-register <= cited license (claim-license check)
  WF6 grounding          grounding.status==grounded requires a receipt that is
                         (verdict==GROUNDED ∧ executed ∧ build_exit==0) AND FRESH —
                         source_sha256 == the LIVE cited .lean's current sha256 (a
                         content-predicate recency check; stale/non-compiling -> reject)

coherency is the WF1-WF4 result (the trust-gradient floor over composed cells);
grounding is the WF6 gate. The two axes never leak into each other.

Usage:
  python3 pap_check.py <doc.pap.json> [--schema pap_ast_v0.1.schema.json]
                       [--proof-index proof_index.json] [--lean-root <dir>]
Exit 0 = COHERENT (no fatal violations). Exit 1 = violations. Exit 2 = bad input.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
_ROOT = HERE.parent  # the repo root (this file lives in <root>/verifier/)
DEFAULT_SCHEMA = HERE / "pap_ast_v0.1.schema.json"
# Optional local proof register(s). Cited ids resolve against these when present;
# if absent, WF1 membership degrades to advisory. Pass --proof-index to point elsewhere.
DEFAULT_PROOF_INDEX = _ROOT / "proof_index_subset.json"
DEFAULT_FRONTIER_INDEX = _ROOT / "frontier_index_subset.json"  # WF1 also resolves candidate ids here
DEFAULT_HELD_INDEX = _ROOT / "held_index_subset.json"          # ...and pre-registration candidate ids here
DEFAULT_LEAN_ROOT = _ROOT / "proofs"  # WF6 hashes the live cited .lean under this root.

GRADIENT = ["NEGATIVE", "UNTESTED", "STRUCTURAL_ANALOG", "CONDITIONAL", "PROVED"]
# coherency floor = the weakest (lowest) trust among composed cells.


class Report:
    def __init__(self):
        self.fatal: list[str] = []
        self.warn: list[str] = []
        self.ok: list[str] = []
        # A STRUCTURED record per fatal, carrying the node names the failing WF actually names —
        # so downstream consumers read typed fields instead of regexing the prose message. Additive:
        # the string `fatal` list is untouched; `names` defaults to [] for callsites that don't supply it.
        self.fatal_records: list[dict] = []

    def fail(self, wf, msg, names=None):
        self.fatal.append(f"{wf}: {msg}")
        self.fatal_records.append({"wf": wf, "msg": msg, "names": list(names or [])})
    def advisory(self, wf, msg): self.warn.append(f"{wf}: {msg}")
    def passed(self, wf, msg): self.ok.append(f"{wf}: {msg}")


def load_proof_ids(path: Path) -> set[str] | None:
    """Return the set of known proof_ids from the proof register, or None if absent.

    The membership set includes the register-local sources WF1 would otherwise miss —
    `entries[*].bond_references` (where BOND-* structural-bond ids live) and
    `structural_proofs[*].proof_id` (structural proofs that are not in `entries`) — so a
    VALID structural-proof / bond citation is not mistaken for drift. (Candidate registers
    are resolved separately by load_proof_registers, which needs their own files.)"""
    if not path.exists():
        return None
    try:
        idx = json.load(open(path))
    except Exception:
        return None
    ids: set[str] = set()
    entries = idx.get("entries", {})
    ents = entries.values() if isinstance(entries, dict) else (entries if isinstance(entries, list) else [])
    if isinstance(entries, dict):
        ids.update(entries.keys())
    for v in ents:
        if isinstance(v, dict):
            if v.get("proof_id"):
                ids.add(v["proof_id"])
            for b in v.get("bond_references", []) or []:   # BOND-* live here, not in structural_proofs
                ids.add(b)
    for sp in idx.get("structural_proofs", []) or []:       # structural proofs
        if isinstance(sp, dict) and sp.get("proof_id"):
            ids.add(sp["proof_id"])
    return ids


def load_proof_registers(proof_index: Path,
                         frontier: Path | None = None,
                         held: Path | None = None) -> dict[str, str] | None:
    """Resolve a cited id against ALL the trust-gradient sources and label it with the REGISTER
    it resolved in, so WF1 distinguishes a valid-but-unscanned citation from real drift
    (resolves NOWHERE). Sources + labels:
      - proof register `entries[*].proof_id`            -> "proved"      (the trust-gradient register)
      - proof register `entries[*].bond_references`     -> "bond"        (BOND-* structural bonds)
      - proof register `structural_proofs[*].proof_id`  -> "structural"  (structural proofs)
      - frontier register `candidates[*].id`            -> "frontier"    (registered, not yet promoted)
      - held register `held_candidates[*].id`           -> "held"        (pre-registration candidates)
    First match wins by precedence (proved > structural > bond > frontier > held), so a token that is
    BOTH a proof and a candidate reports the stronger register. Returns None if the proof register is
    absent (WF1 membership advisory is then skipped)."""
    if not proof_index.exists():
        return None
    reg: dict[str, str] = {}
    def add(idval, label):
        if idval and idval not in reg:   # first (= strongest, by call order below) wins
            reg[idval] = label
    try:
        idx = json.load(open(proof_index))
    except Exception:
        return None
    entries = idx.get("entries", {})
    ents = entries.values() if isinstance(entries, dict) else (entries if isinstance(entries, list) else [])
    if isinstance(entries, dict):
        for k in entries:
            add(k, "proved")
    for v in ents:
        if isinstance(v, dict) and v.get("proof_id"):
            add(v["proof_id"], "proved")
    for sp in idx.get("structural_proofs", []) or []:
        if isinstance(sp, dict):
            add(sp.get("proof_id"), "structural")
    for v in ents:
        if isinstance(v, dict):
            for b in v.get("bond_references", []) or []:
                add(b, "bond")
    for f, label, key in ((frontier or DEFAULT_FRONTIER_INDEX, "frontier", "candidates"),
                          (held or DEFAULT_HELD_INDEX, "held", "held_candidates")):
        try:
            if Path(f).exists():
                doc = json.load(open(f))
                for c in doc.get(key, []) or []:
                    if isinstance(c, dict):
                        add(c.get("id") or c.get("cambium_id") or c.get("candidate_id"), label)
        except Exception:
            pass
    return reg


def load_proof_entries(path: Path) -> dict | None:
    """Return {proof_id -> entry} from the proof register (for WF5 license derivation), or None
    if absent. Tolerates the {entries:[...]} / {entries:{...}} shapes and a bare map."""
    if not path.exists():
        return None
    try:
        idx = json.load(open(path))
    except Exception:
        return None
    out: dict[str, dict] = {}
    entries = idx.get("entries") if isinstance(idx, dict) else None
    if isinstance(entries, list):
        for v in entries:
            if isinstance(v, dict) and v.get("proof_id"):
                out[v["proof_id"]] = v
    elif isinstance(entries, dict):
        for k, v in entries.items():
            if isinstance(v, dict):
                out[v.get("proof_id", k)] = v
    elif isinstance(idx, dict):
        for k, v in idx.items():
            if isinstance(v, dict) and ("status" in v or "proof_file" in v):
                out[v.get("proof_id", k)] = v
    return out or None


def wf1_resolve(doc, proof_ids, r: Report):
    """`proof_ids` is either the membership SET (load_proof_ids — back-compat) or the
    REGISTER MAP (load_proof_registers — id -> 'proved'/'structural'/'bond'/'frontier'/'held'). When it
    is the map, WF1 reports the RESOLVED REGISTER on a pass and only advises on a citation that resolves
    NOWHERE (real drift) — a valid bond/structural/candidate citation must not read as drift."""
    cells = doc.get("cells", {})
    if not cells:
        r.passed("WF1", "no cells to resolve (vacuous)")
        return
    for name, c in cells.items():
        trust = c.get("trust")
        ref = c.get("proof_ref")
        register = proof_ids.get(ref) if isinstance(proof_ids, dict) else None
        if trust and trust != "UNTESTED" and not ref:
            r.fail("WF1", f"cell '{name}' is {trust} but has no proof_ref", names=[name])
        elif ref and proof_ids is not None and ref not in proof_ids:
            r.advisory("WF1", f"cell '{name}' proof_ref '{ref}' resolves NOWHERE — not in "
                              f"entries/bonds/structural_proofs/frontier/held (real drift, or a freshly "
                              f"coined id awaiting registration)")
        elif register:
            r.passed("WF1", f"cell '{name}' resolves (register: {register})")
        else:
            r.passed("WF1", f"cell '{name}' resolves")


def wf2_negative(doc, r: Report):
    bad = [n for n, c in doc.get("cells", {}).items() if c.get("trust") == "NEGATIVE"]
    if bad:
        r.fail("WF2", f"NEGATIVE cell(s) composed (forbidden): {bad}", names=bad)
    else:
        r.passed("WF2", "no NEGATIVE cells")


def wf3_frame_primacy(doc, r: Report):
    for name, e in doc.get("expressions", {}).items():
        kind = e.get("kind", "frame_bound")
        frame = e.get("frame")
        primary = e.get("primary")
        if kind != "invariant" and not frame:
            r.fail("WF3", f"expression '{name}' is frame_bound but names no frame", names=[name])
            continue
        if primary and not frame:
            r.fail("WF3", f"expression '{name}' asserts primacy '{primary}' with no frame (GLOBAL primacy forbidden)", names=[name])
            continue
        r.passed("WF3", f"expression '{name}' frame-ok" + (f", primacy frame-relative to {frame}" if primary else ""))


def wf4_open_mouth(doc, r: Report):
    """A cycle in the expression compose/via graph is legal only if some node on it
    carries a grounding receipt (open-mouth)."""
    exprs = doc.get("expressions", {})
    # edges: expression -> referenced expression (composed or via-bond not modeled here)
    graph = {n: [c for c in e.get("compose", []) if c in exprs] for n, e in exprs.items()}
    grounded = {n for n, e in exprs.items()
                if e.get("orientation", {}).get("grounding", {}).get("status") == "grounded"}
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {n: WHITE for n in graph}
    cyclic_nodes: set[str] = set()

    def dfs(u, stack):
        color[u] = GRAY
        stack.append(u)
        for v in graph.get(u, []):
            if color[v] == GRAY:
                i = stack.index(v)
                cyclic_nodes.update(stack[i:])
            elif color[v] == WHITE:
                dfs(v, stack)
        stack.pop()
        color[u] = BLACK

    for n in graph:
        if color[n] == WHITE:
            dfs(n, [])
    if not cyclic_nodes:
        r.passed("WF4", "compose graph acyclic")
    elif cyclic_nodes & grounded:
        r.passed("WF4", f"cycle present but open-mouth (passes grounding node {cyclic_nodes & grounded})")
    else:
        r.fail("WF4", f"closed self-referential cycle with no grounding node: {sorted(cyclic_nodes)}", names=sorted(cyclic_nodes))


# WF5 register ladder. A claim's prose register may not exceed the license its cited
# proof grants. `empirical` (a world-contact / physical-substrate assertion) is licensed
# by NO proof — it requires a fresh world-contact receipt (WF6), not coherency — so an
# empirical register over a Lean citation is the canonical over-claim (a structural theorem
# narrated as a world-measurement). This is the prose-faithfulness rung.
REGISTER_RANK = {"neutral": 0, "analogy": 1, "structural": 2, "substrate": 3, "empirical": 4}


def _license_rank(entry: dict | None) -> int:
    """The strongest register a cited proof entry licenses.
      PROVED structural/bridge proof -> `structural` (2): an algebraic correspondence.
      PROVED substrate-bound pattern  -> `substrate` (3): a substrate-faithful derivation.
      CONDITIONAL                     -> `structural` (2), with stated preconditions.
      anything weaker / unresolved    -> `analogy` (1).
    No proof ever licenses `empirical` (4) — world-contact is WF6's gate, not WF5's."""
    if entry is None:
        return 1
    status = entry.get("status")
    pat = str(entry.get("pattern_id", "")).upper()
    if status == "PROVED":
        return 2 if ("BRIDGE" in pat or "STRUCTURAL" in pat) else 3
    if status == "CONDITIONAL":
        return 2
    return 1


def wf5_license(doc, proof_entries, r: Report):
    """FIRES on CLAIM cells (cells carrying a `claim`): the claim's register must not exceed
    the license of the proof cell(s) it is BONDED to. A claim with no bonded cited authority
    cannot be licensed at all (> neutral is an over-claim)."""
    cells = doc.get("cells", {})
    claim_cells = {n: c for n, c in cells.items() if "claim" in c}
    if not claim_cells:
        renders = doc.get("renders", {})
        if renders:
            r.advisory("WF5", f"{len(renders)} render(s), no CLAIM cells — no prose-register assertion to audit")
        else:
            r.passed("WF5", "no claims (vacuous)")
        return
    bonds = doc.get("bonds", {})

    def cited_license_for(claim_name: str) -> tuple[int, list[str]]:
        """The FLOOR (weakest) license over every proof cell bonded to this claim cell,
        and the proof_refs that set it. No bonded authority -> neutral-only (rank 0)."""
        refs: list[str] = []
        ranks: list[int] = []
        for b in bonds.values():
            members = b.get("cells", [])
            if claim_name not in members:
                continue
            for m in members:
                cc = cells.get(m, {})
                pr = cc.get("proof_ref")
                if not pr or m == claim_name:
                    continue
                refs.append(pr)
                ranks.append(_license_rank((proof_entries or {}).get(pr)))
        if not ranks:
            return 0, []  # no bonded cited authority -> licenses only `neutral`
        return min(ranks), refs

    for name, c in claim_cells.items():
        reg = c["claim"].get("register", "neutral")
        reg_rank = REGISTER_RANK.get(reg, 0)
        lic_rank, refs = cited_license_for(name)
        lic_reg = next((k for k, v in REGISTER_RANK.items() if v == lic_rank), "neutral")
        if not refs:
            r.fail("WF5", f"claim cell '{name}' register '{reg}' but no bonded cited authority "
                          f"(an uncited claim licenses only 'neutral')")
        elif reg_rank > lic_rank:
            r.fail("WF5", f"claim cell '{name}' OVER-CLAIMS: register '{reg}' exceeds license "
                          f"'{lic_reg}' granted by cited {refs} "
                          f"({'empirical needs a world-contact receipt (WF6), not a Lean proof' if reg == 'empirical' else 'narrows to the cited proof'})")
        else:
            r.passed("WF5", f"claim cell '{name}' register '{reg}' <= license '{lic_reg}' (cited {refs})")


def _sha256_file(path: Path) -> str | None:
    try:
        import hashlib
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except Exception:
        return None


def _receipt_is_fresh(rec: dict, lean_root: Path) -> tuple[bool, str]:
    """The recency check. Freshness is a CONTENT PREDICATE, not a stamp string and not mtime: the
    receipt is FRESH iff the LIVE cited .lean's current sha256 equals the receipt's source_sha256 — a
    genuine world-contact (WF6 must HASH the live file). A Mathlib/toolchain drift stales it too. A
    stale / sha-drifted receipt is NOT fresh -> WF6 rejects the `grounded` label."""
    lf = rec.get("lean_file")
    want_sha = rec.get("source_sha256")
    if not lf or not want_sha:
        return False, "receipt missing lean_file/source_sha256 (cannot verify world-contact)"
    p = (lean_root / lf)
    if not p.exists():
        # try stripping a leading 'LEAN/' since lean_root already points at the LEAN dir
        alt = lean_root / Path(lf).relative_to("LEAN") if str(lf).startswith("LEAN/") else None
        if alt and alt.exists():
            p = alt
        else:
            return False, f"cited lean_file '{lf}' not found under lean_root '{lean_root}' (cannot confirm freshness)"
    live = _sha256_file(p)
    if live is None:
        return False, f"could not read live '{lf}' to hash (world-contact unverifiable)"
    if live != want_sha:
        return False, (f"STALE: source_sha256 drift — receipt {want_sha[:12]}… != live {live[:12]}… "
                       f"(the .lean changed since the build; re-witness)")
    # toolchain drift (cheap, in lean_root)
    tc = rec.get("lean_toolchain")
    if tc:
        tcf = lean_root / "lean-toolchain"
        if tcf.exists() and tcf.read_text().strip() != tc.strip():
            return False, "STALE: lean_toolchain drift since the build"
    # mathlib rev drift (from the live manifest)
    mr = rec.get("mathlib_rev")
    if mr:
        man = lean_root / "lake-manifest.json"
        if man.exists():
            try:
                pkgs = json.load(open(man)).get("packages", [])
                liverev = next((x.get("rev") for x in pkgs if x.get("name") == "mathlib"), None)
                if liverev and liverev != mr:
                    return False, "STALE: mathlib_rev drift since the build"
            except Exception:
                pass
    return True, (f"FRESH: source_sha256 matches live {lf} ({live[:12]}…), toolchain+mathlib_rev match")


def _project_root() -> Path | None:
    """Resolve a project root for a relative `adopter_ref`, INVARIANT to invocation cwd.

    Returns the nearest ancestor containing a `.git` directory (the project root marker), or
    None if none is found. The function NEVER falls back to Path.cwd(): a silent cwd fallback
    would resolve a root-relative ref against the wrong tree and misnarrate a still-grounded
    adoption as STALE/withdrawn. The caller fails loud instead."""
    for a in (HERE, *HERE.parents):
        if (a / ".git").exists():
            return a
    return None


def _social_receipt_is_fresh(rec: dict) -> tuple[bool, str]:
    """The recency check for a NON-computational, observational world-contact (mechanism ==
    witnessed_adoption) — the WF6 analog of `_receipt_is_fresh`. Freshness is a CONTENT PREDICATE on
    the ADOPTER artifact (not on a cited .lean): the receipt is FRESH iff `adopter_ref` still EXISTS
    and still CONTAINS `citation_token` at check time — i.e. the adoption RELATIONSHIP persists.
    Un-adoption (the adopter removed the reference) -> NOT fresh -> WF6 rejects `grounded`. Unrelated
    edits to the adopter artifact do NOT stale it (only removing the token does); a recorded
    `adopter_source_sha256` is provenance, not the staling predicate. The social analog of the
    source_sha256 content-freshness that gates a build receipt."""
    ref = rec.get("adopter_ref")
    tok = rec.get("citation_token")
    if not ref or not tok:
        return False, "social receipt missing adopter_ref/citation_token (cannot verify the adoption)"
    p = Path(ref)
    resolved_root = None
    if not p.is_absolute():
        resolved_root = _project_root()
        if resolved_root is None:
            # Fail LOUD, not silent-cwd: we could not locate the project root, so a root-relative
            # adopter_ref is UNVERIFIABLE here. Critically this is NOT narrated as withdrawal — a
            # false-STALE would flip a still-grounded adoption to FLOATING on a phantom. WF6 stays
            # conservative (rejects grounding it cannot verify) without asserting the adoption was removed.
            return False, (f"UNVERIFIABLE: could not locate project root to resolve relative adopter_ref "
                           f"'{ref}' (NOT a withdrawal — invoke from within the project tree to re-check)")
        p = resolved_root / ref
    if not p.exists():
        return False, f"STALE: adopter artifact '{ref}' not found (adoption withdrawn / artifact moved)"
    try:
        body = p.read_text(errors="replace")
    except Exception:
        return False, f"could not read adopter artifact '{ref}' (adoption unverifiable)"
    if tok not in body:
        return False, (f"STALE: adopter '{ref}' no longer cites '{tok}' "
                       f"(un-adopted since the witness — re-witness)")
    root_note = f" [root: {resolved_root}]" if resolved_root is not None else " [adopter_ref absolute]"
    return True, f"FRESH: adopter '{ref}' still cites '{tok}' (adoption relationship persists){root_note}"


def wf6_grounding(doc, r: Report, lean_root: Path):
    """WF6 ACCEPT branch: a `grounded` label is earned ONLY by a receipt that is
    (a) a real, executed, GROUNDED world-contact (verdict==GROUNDED ∧ executed ∧ build_exit==0
    — a NON-COMPILING build is rejected) AND (b) FRESH by the content predicate above (a stale /
    sha-drifted receipt is rejected). Grounding is NEVER inherited from coherency; a PROVED
    citation raises coherency, not grounding — only a fresh executed build raises grounding."""
    receipts = doc.get("receipts", {})
    any_grounded = False
    for name, e in doc.get("expressions", {}).items():
        g = e.get("orientation", {}).get("grounding", {})
        if g.get("status") != "grounded":
            continue
        any_grounded = True
        ref = g.get("receipt")
        if not ref or ref not in receipts:
            r.fail("WF6", f"expression '{name}' grounded but has no resolvable receipt")
            continue
        rec = receipts[ref]
        # --- SOCIAL grounding branch (witnessed_adoption): an observational world-contact, NOT a
        #     kernel build. WF6 keys on verdict==GROUNDED + the social freshness predicate (the adopter
        #     still cites the work) + honest-N (Condition C). The KIND lives in `mechanism`; the axis
        #     (R-level) stays orthogonal (Condition B). The computational checks below are SKIPPED. ---
        if rec.get("mechanism") == "witnessed_adoption":
            verdict = rec.get("verdict")
            if verdict and verdict != "GROUNDED":
                r.fail("WF6", f"expression '{name}' social receipt '{ref}' verdict is '{verdict}', not GROUNDED "
                              f"(a non-GROUNDED adoption does NOT earn grounding — stay floating)")
                continue
            if not rec.get("freshness"):
                r.fail("WF6", f"expression '{name}' social receipt '{ref}' has no freshness stamp")
                continue
            # Condition C — honest N: adopter_count must equal the number of DISTINCT adopters (one
            # acknowledgement + the same adopter's edit is N=1, correlated not independent), and a
            # stronger axis (R2/R3) may NOT be claimed on a single adopter (over-claim guard).
            adopters = rec.get("adopters") or []
            count = rec.get("adopter_count")
            if count is None or len(adopters) != count:
                r.fail("WF6", f"expression '{name}' social receipt '{ref}': adopter_count={count} != "
                              f"len(adopters)={len(adopters)} (honest-N violated)")
                continue
            if len(set(adopters)) != len(adopters):
                r.fail("WF6", f"expression '{name}' social receipt '{ref}': duplicate adopters "
                              f"(one adopter double-counted via ack+edit — not independent)")
                continue
            axis = rec.get("axis") or g.get("axis")
            if axis in ("R2", "R3") and (count or 0) < 2:
                r.fail("WF6", f"expression '{name}' social receipt '{ref}' claims {axis} with only N={count} "
                              f"adopter — OVER-CLAIM (one ack is N=1, not corroboration; R2+ needs >=2 "
                              f"independent adopters)")
                continue
            fresh, why = _social_receipt_is_fresh(rec)
            if not fresh:
                r.fail("WF6", f"expression '{name}' social receipt '{ref}' is NOT fresh — {why}")
                continue
            r.passed("WF6", f"expression '{name}' grounded by FRESH social receipt '{ref}' "
                            f"(witnessed_adoption, verdict GROUNDED, N={count}; {why})")
            continue
        # (a) real, executed, GROUNDED world-contact — the anti-spoof / non-compiling guard
        verdict = rec.get("verdict")
        if verdict and verdict != "GROUNDED":
            r.fail("WF6", f"expression '{name}' receipt '{ref}' verdict is '{verdict}', not GROUNDED "
                          f"(a DIVERGENT/UNVERIFIABLE world-contact does NOT earn grounding — stay floating)")
            continue
        if rec.get("executed") is False:
            r.fail("WF6", f"expression '{name}' receipt '{ref}' was not executed "
                          f"(an inferred-not-run build does NOT earn grounding)")
            continue
        if rec.get("build_exit") not in (0, None):
            r.fail("WF6", f"expression '{name}' receipt '{ref}' build did NOT compile "
                          f"(build_exit={rec.get('build_exit')} != 0); a non-compiling build does not ground")
            continue
        if not rec.get("freshness"):
            r.fail("WF6", f"expression '{name}' receipt '{ref}' has no freshness stamp")
            continue
        # (b) the REAL recency check — hash the live cited .lean (world-contact)
        fresh, why = _receipt_is_fresh(rec, lean_root)
        if not fresh:
            r.fail("WF6", f"expression '{name}' receipt '{ref}' is NOT fresh — {why}")
            continue
        r.passed("WF6", f"expression '{name}' grounded by FRESH receipt '{ref}' "
                        f"(verdict GROUNDED, build exit 0; {why})")
    if not any_grounded:
        r.passed("WF6", "all expressions floating (honestly labeled; no grounded claim to back)")


# The bounded prover-CORROBORATION gate. An `prover_corroboration` receipt is an INDEPENDENT-PROVER
# check that the cited statement is genuinely re-provable — a real external contact DISTINCT from the
# kernel `lake build`, but NOT a stronger grounding tier. This gate does NOT touch the R-axis; it only
# validates that a receipt CLAIMING corroboration actually carries an accepted prover verdict: a receipt
# claiming corroboration with NO prover_verdict (re-proved, sorry-count 0) is REJECTED — corroboration
# without a verdict earns nothing.
ACCEPTED_PROVER_STATUSES = {"re-proved", "reproved", "RE_PROVED", "re_proved", "proved"}


def wf6_prover_corroboration(doc, r: Report):
    receipts = doc.get("receipts", {})
    corrob_receipts = {n: rec for n, rec in receipts.items()
                       if rec.get("mechanism") == "prover_corroboration"}
    # (1) Every expression that REFERENCES a corroboration must resolve it to a corrob receipt.
    for name, e in doc.get("expressions", {}).items():
        for cref in (e.get("orientation", {}).get("grounding", {}).get("corroborations") or []):
            if cref not in receipts:
                r.fail("WF6c", f"expression '{name}' names corroboration '{cref}' with no resolvable receipt")
            elif receipts[cref].get("mechanism") != "prover_corroboration":
                r.fail("WF6c", f"expression '{name}' corroboration '{cref}' is not a "
                               f"prover_corroboration receipt (mechanism "
                               f"'{receipts[cref].get('mechanism')}')")
    # (2) Every prover_corroboration receipt must carry a prover + an ACCEPTED prover_verdict.
    for n, rec in corrob_receipts.items():
        prover = rec.get("prover")
        if not prover:
            r.fail("WF6c", f"corroboration receipt '{n}' has no `prover` "
                           f"(a prover-less corroboration earns nothing)")
            continue
        pv = rec.get("prover_verdict")
        if not pv or not isinstance(pv, dict):
            r.fail("WF6c", f"corroboration receipt '{n}' claims corroboration but carries "
                           f"NO `prover_verdict` — REJECT (corroboration without a verdict is empty)")
            continue
        status = pv.get("status")
        sc = pv.get("sorry_count")
        if status not in ACCEPTED_PROVER_STATUSES:
            r.fail("WF6c", f"corroboration receipt '{n}' prover_verdict status '{status}' is not an "
                           f"accepted re-prove verdict ({sorted(ACCEPTED_PROVER_STATUSES)})")
            continue
        if sc != 0:
            r.fail("WF6c", f"corroboration receipt '{n}' prover_verdict sorry_count is {sc} != 0 "
                           f"(an incomplete re-prove does NOT corroborate)")
            continue
        r.passed("WF6c", f"corroboration receipt '{n}' carries an accepted prover verdict "
                         f"(prover '{prover}', status '{status}', sorry-count 0) — independent "
                         f"re-prove CORROBORATES (cross-prover breadth, NOT a stronger R-tier)")
    if not corrob_receipts:
        r.passed("WF6c", "no prover-corroboration receipts (nothing to corroborate; grounding unaffected)")


def compute_coherency(doc) -> dict[str, str]:
    """coherency floor = weakest trust among composed CELLS. Terms-only exprs are
    declared (no cell evidence) — reported as authored with a note."""
    cells = doc.get("cells", {})
    out = {}
    for name, e in doc.get("expressions", {}).items():
        composed_cells = [cells[c]["trust"] for c in e.get("compose", [])
                          if c in cells and "trust" in cells[c]]
        authored = e.get("orientation", {}).get("coherency")
        if composed_cells:
            floor = min(composed_cells, key=lambda t: GRADIENT.index(t))
            out[name] = f"{floor} (computed floor)" + ("" if floor == authored else f" != authored {authored} ⚠")
        else:
            out[name] = f"{authored} (declared; no cell evidence)"
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("doc")
    ap.add_argument("--schema", default=str(DEFAULT_SCHEMA))
    ap.add_argument("--proof-index", default=str(DEFAULT_PROOF_INDEX))
    ap.add_argument("--frontier-index", default=str(DEFAULT_FRONTIER_INDEX),
                    help="WF1 also resolves cited ids against this candidate register.")
    ap.add_argument("--held-index", default=str(DEFAULT_HELD_INDEX),
                    help="WF1 also resolves cited ids against this pre-registration candidate register.")
    ap.add_argument("--lean-root", default=str(DEFAULT_LEAN_ROOT),
                    help="root the cited .lean paths resolve under — WF6 hashes the LIVE file "
                         "for the content-predicate freshness check (a stale receipt -> reject).")
    args = ap.parse_args()

    try:
        doc = json.load(open(args.doc))
    except Exception as ex:
        print(f"ERROR loading doc: {ex}", file=sys.stderr); return 2

    # Structural gate (schema) first.
    try:
        import jsonschema
        jsonschema.validate(doc, json.load(open(args.schema)))
        schema_line = "schema: VALID ✓"
    except ImportError:
        schema_line = "schema: SKIPPED (jsonschema not installed)"
    except Exception as ex:
        print(f"schema: INVALID ✗ — {ex}", file=sys.stderr); return 1

    proof_registers = load_proof_registers(Path(args.proof_index),
                                            Path(args.frontier_index), Path(args.held_index))
    proof_entries = load_proof_entries(Path(args.proof_index))
    r = Report()
    wf1_resolve(doc, proof_registers, r)
    wf2_negative(doc, r)
    wf3_frame_primacy(doc, r)
    wf4_open_mouth(doc, r)
    wf5_license(doc, proof_entries, r)
    wf6_grounding(doc, r, Path(args.lean_root))
    wf6_prover_corroboration(doc, r)

    print(f"=== PAP check: {args.doc} ===")
    print(schema_line)
    print(f"proof_index: {'loaded ' + str(len(proof_registers)) + ' ids (entries+bonds+structural+frontier+held)' if proof_registers else 'not found (WF1 membership advisory skipped)'}")
    print("\n-- gyroscope (coherency axis, computed) --")
    for n, v in compute_coherency(doc).items():
        print(f"  {n}: {v}")
    print("\n-- passes --")
    for line in r.ok:    print(f"  PASS  {line}")
    for line in r.warn:  print(f"  WARN  {line}")
    for line in r.fatal: print(f"  FAIL  {line}")

    if r.fatal:
        print(f"\nRESULT: INCOHERENT ✗ ({len(r.fatal)} violation(s))")
        return 1
    print(f"\nRESULT: COHERENT ✓ ({len(r.warn)} advisory)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
