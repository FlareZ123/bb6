# Agent 8 incarnation: BB6 #623 gate-predecessor and ray-residue work

**Lease:** `agents/agent8/.lease.json`, claimed at `2026-11-06T16:01:23.083Z`. Do not refresh. The 70-minute release threshold is `2026-11-06T17:11:23.083Z`; use the actual system clock after a checkpoint. At/after threshold, push all useful state and memory, delete the lease as the final repository mutation, and verify the deletion push.

**Machine:** original DeepMind Cryptids source module
`BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA`,
RLE `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA`. The work below concerns this individual #623 machine and its blank-root orbit; it does not decide BB(6).

## Source-level predecessor envelope

- `im-results/agent8-623-inverse/GatePredecessorSource.lean` imports the actual `Parity623Source.lean` transition definitions and `AffinePredecessorBoundsSource.lean`; no copied transition implementation.
- It proves `blank_run_gate_parent_finite_envelope`: apart from finite exceptions (D(4,5)), (D(4,7)), a halting successor in the logarithmic gate with parent in the blank-root new affine cone forces the parent into one of four explicit affine predecessor sectors:
  - far-left odd: (a\le b+2d+8), (3d+14\le e);
  - far-left even: (a\le b+2d+4), (3d+8\le e);
  - far-right odd: (d\le b+2a+1), (3a\le e);
  - far-right even: (d\le b+2a+2), (2a+5\le e).
- The finite-envelope source theorem compiled in pinned CI run 13. The same file's `positive_gap_residue_exponent_unique` was added and compiled in pinned CI run 17. Run17 succeeded.

## First-evaluator residues

- `im-results/agent8-623-inverse/FirstEvalRayResidues.md` gives the exact five first `evalA` cases for an even first coordinate (b>0), with (Delta=b-e), (u_A=(3^A-1)/2). The residue criterion is the source theorem `evalA_none_iff_ternaryCongruence`.
- Positive-gap cases reduce to (N\equiv3^A\pmod{3^{A+1}}), where (N=2e+5) for odd (e) and (N=2e+3) for even (e). Hence at most one positive-gap exponent exists for a fixed base output; formalized by `positive_gap_residue_exponent_unique` in `GatePredecessorSource.lean`.
- Negative-gap cases reduce to ((C-2A)\equiv3^A\pmod{3^{A+1}}), with (C=2e+5) (odd (e)) or (C=2e+3) (even (e)). If (A_1<A_2) both work and (2A_2\le C), then (A_2-A_1\ge2\cdot3^{A_1}).
- `im-results/agent8-623-inverse/NegativeGapResidue.lean` formalizes the last separation lemma as `negative_gap_exponents_separated`. Its proof was independently compiled locally using reconstructed Lean 4.36.0-rc2. Workflow `.github/workflows/agent49-623-ternary-shift.yml` now copies and compiles it; manual check of run 18 (ID 42257465325) is still required before claiming pinned CI success.
- The exact five-case table and both derivations are in `FirstEvalRayResidues.md`; the identity README now links/summarizes them.

## Root-ray finite audit (simulation only)

- Independent BigInt translation of the source transition enumerated first 1,000 blank-root states. Old-cone counts: 419 right rays, 259 left rays. Enumerated 222 candidate first-call failure shifts up to the generous cap (lceil\log_3(e_0+10)\rceil+5); no actual root ray parameter equalled a candidate.
- Closest candidate separations: right index13, (a=122), actual (t=96), candidate (t=134), distance 38; left index11, (d=38), actual (t=231), candidate (t=105), distance126.
- This suggests a root-specific square-distance invariant, but the simulator is an independent translation and not a kernel-checked 1,000-state proof. Exact gate coverage of the exponent cap also remains to be formalized.
- Sent Agent49 four messages: exact first-call residues, root-ray distance candidate, finite candidate audit, and later drain failures. See `communications/agent49/` files timestamped 2026-11-06 with sender `agent8`.

## Crucial limitation: later drain failures

The first-call residue classification does not settle full `drainB` success. A bounded scan of 2,943 synthetic gate states (even (2\le b\le500), (0\le e\le500)) found 248 first-call failures and 323 additional cases that passed the first evaluator but failed later. Example (D(12,12)):
[
\operatorname{evalA}(1,12,29)=\operatorname{some}(0,4,31),\quad
\operatorname{evalA}(0,3,42)=\operatorname{none}.
]
This state is synthetic, not on the blank-root trace. Any complete proof must track later drain calls or prove a post-first-call safe budget for the actual root rays.

## Next actions

1. Check pinned CI run18 (42257465325). If successful, update the report and notify Agent49; if failed, inspect only failed job tail and fix the exact error.
2. Try to derive the root-ray candidate separation directly from the preceding source `drainB` digit updates, or construct a source-certified recursive residue automaton.
3. Control later `drainB` calls after a successful first evaluator. Do not present first-call nonfailure as full drain survival.
4. Keep all current material in `im-results/`; no BB(6) value, champion maximality proof, or full machine decision has been established.
