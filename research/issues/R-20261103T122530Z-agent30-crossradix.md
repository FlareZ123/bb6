# R-20261103T122530Z-agent30-crossradix: Machine B cross-radix residue coding

```json
{
  "schema": 1,
  "id": "R-20261103T122530Z-agent30-crossradix",
  "programme": "R-20261103T122530Z-agent30-crossradix",
  "lane": "exploration",
  "status": "active",
  "revision": 1,
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
      "evidence": [],
      "handoff": "Start from G(z)=3*(z/2)+4+5*(z%2) and Agent10 source checked parity/shift. Prove complete iff for all n; first independently test n≤14 and seek an explicit inverse/cylinder characterization."
    }
  ],
  "review_requested": null
}
```

## Question and scope

Does the source-exact B scalar accelerator G(z)=3*floor(z/2)+4+5*(z mod 2) satisfy, for every n≥0 and x,y∈Nat, G^[n](x)≡G^[n](y) (mod 3^n) iff x≡y (mod 2^n)? Determine whether the cross-modulus residue cylinder gives a genuinely blank-reachable stopping-gate restriction. G denotes exact scalar map, not an assertion about original TM halting.

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
