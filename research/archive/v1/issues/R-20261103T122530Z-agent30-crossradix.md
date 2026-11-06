# Archived original investigation: Machine B: cross-radix and affine-quotient limitations

The complete dated issue text is preserved below, including mathematical leads, proof links, counterexamples and retired accounting. Its execution statuses and grant decisions are historical. See [current scientific summary](../../../issues/R-20261103T122530Z-agent30-crossradix.md).

---

> **Super-Critic correction, maintainer-authorized 2026-11-03:** v1 grants, slots, claim accounting, required formats and renewal permissions below are retired. Preserve and use the scientific evidence. No checker is required. You need not read or update historical claim arrays; use the board's scientific-note links. [Current guide](../../../../RESEARCH_PROTOCOL.md) · [Readable board](../../../BOARD.md).

# R-20261103T122530Z-agent30-crossradix: Machine B cross-radix residue coding

```json
{
  "schema": 1,
  "id": "R-20261103T122530Z-agent30-crossradix",
  "programme": "R-20261103T122530Z-agent30-crossradix",
  "lane": "exploration",
  "status": "active",
  "revision": 2,
  "parallel_limit": 2,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 30",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T122530Z-agent30-crossradix.md"
    }
  ],
  "claims": [
    {
      "id": "agent30:agent30-bb6-20261103T121932117Z:R-20261103T122530Z-agent30-crossradix",
      "agent": "agent30",
      "run_id": "agent30-bb6-20261103T121932117Z",
      "claimed_at": "2026-11-03T12:19:32.117Z",
      "registered_at": "2026-11-03T12:25:54.624Z",
      "grant": 1,
      "task_issue": "R-20261103T122530Z-agent30-crossradix",
      "task": "Test whether the exact Machine B scalar G^n outputs modulo 3^n encode precisely input residues modulo 2^n, using source-consistent proofs; assess consequences for genuine blank reset gates.",
      "role": "investigate",
      "state": "active",
      "evidence": [
        {
          "kind": "kernel-proof",
          "path": "im-results/agent30-b-crossradix/Agent30CrossRadix.lean",
          "note": "All n,x,y,m cross-radix (3^n*m output iff 2^n*m input), locally Lean4.36 verified; no sorry"
        },
        {
          "kind": "kernel-proof",
          "path": "im-results/agent30-b-crossradix/Agent30BFiniteFactor.lean",
          "note": "All n>0,m>0 complete arbitrary residue-quotient classification iff m divides7; strict extension of R007 affine-only classification; local Lean4.36 standard axioms"
        },
        {
          "kind": "kernel-proof",
          "path": "im-results/agent30-b-crossradix/Agent30CrossRadixCantor.lean",
          "note": "Canonical 2^n input residues inject into 3^n output classes; exact cover"
        },
        {
          "kind": "kernel-proof",
          "path": "im-results/agent30-b-crossradix/Agent30CrossRadixParity.lean",
          "note": "All-n dyadic output shift and same 3^n residue, opposite parity witness; limitation of sieve"
        },
        {
          "kind": "kernel-proof",
          "path": "im-results/agent30-b-crossradix/Agent30CrossRadixWord.lean",
          "note": "Exact all-n weighted parity-word representation"
        },
        {
          "kind": "source-bridge-pending",
          "path": "im-results/agent30-b-crossradix/Agent30FiniteFactorSource.lean",
          "note": "Local scratch-stub checked; full original Agent18 BOneDim CI 41640186396 failed before steps, verification still pending"
        },
        {
          "kind": "reproducer",
          "path": "im-results/agent30-b-crossradix/residue_membership.py",
          "note": "O(n) reverse-radix sieve exhaustively agrees with true outputs n≤12; no kernel proof of algorithm"
        },
        {
          "kind": "synthesis",
          "path": "im-results/agent30-b-crossradix/README.md",
          "note": "Scope, novelty caveat, exact source provenance and root limitation"
        }
      ],
      "handoff": "Source-authentic original Agent18 bridge still pending CI runner availability (two consecutive 4s pre-step failures, log HTTP404). New locally kernel-proved all-iterate finite-congruence-factor iff m|7 extends earlier affine-only result, but no BB6 root decision and likely classical symbolic dynamics prior art; adversarially check significance and overlap. Further seed-zero parity-gate work needs a qualitatively new invariant; universal output residue sieves cannot determine bit because shifted seed 2^n flips bit at fixed mod3^n."
    }
  ],
  "review_requested": null
}
```

## Question and scope

Does the source-exact B scalar accelerator G(z)=3*floor(z/2)+4+5*(z mod 2) satisfy, for every n≥0 and x,y∈Nat, G^[n](../../x)≡G^[n](../../y) (mod 3^n) iff x≡y (mod 2^n)? Determine whether the cross-modulus residue cylinder gives a genuinely blank-reachable stopping-gate restriction. G denotes exact scalar map, not an assertion about original TM halting.

## Baseline and overlap

Agent10's already source-certified dyadic input-shift and parity-prefix bijections, Agent18 B scalar-to-source bridge, and Agent30's R007 all-input affine same-modulus obstruction are prior evidence. This pilot studies a *nonlinear cross-modulus 2-adic to 3-adic* equivalence, including inverse residues and seed-specific use; it does not split R007's same-modulus affine classification or claim its prior results as new. Standard generalized Collatz conjugacies could be external prior art; novelty must be assessed separately.

## Approach and discriminating tests

Compute exact output collision counts for n=1..14 and search a minimal counterexample. Prove an inverse step: G(x) ≡ G(y) (mod 3^(k+1)) iff x ≡ y (mod 2*3^k); then iterate, taking care that intermediate parity and 3-adic divisibility propagate backwards. Test whether stopping reset values are excluded by the resulting Cantor residue subset, rather than assuming they are. Exact source import and Lean are desirable; a finite observation is not proof.

## Outcomes and renewal

Deliver all-n proof, explicit failing inputs, or precise unresolved induction. Evaluate a meaningful blank-reachable consequence. If merely a known coding identity that does not constrain root stopping, record negative evidence and avoid routine residue extensions.

## Compute

Local small finite enumeration through n=14 first, exact integers; no new per-commit CI. Use local Lean 4.36 if helpful; only request existing manual CI if source-connected formal claim is ready.

## Next action and handoff

Formalize the all-n congruence equivalence with exact n-step map and an explicit source connection, then apply to the seed-zero and reset-index predicate. No BB6 root decision or bound improvement is asserted.
