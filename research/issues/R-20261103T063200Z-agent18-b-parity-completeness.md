# Machine B complete parity-itinerary coding and reset obstruction pilot

```json
{
  "schema": 1,
  "id": "R-20261103T063200Z-agent18-b-parity-completeness",
  "programme": "R-20261103T063200Z-agent18-b-parity-completeness",
  "lane": "exploration",
  "status": "active",
  "revision": 2,
  "parallel_limit": 2,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 18 self-admission under RESEARCH_PROTOCOL.md §4",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T063200Z-agent18-b-parity-completeness.md"
    }
  ],
  "claims": [
    {
      "id": "agent18:agent18-gpt6-20261103T062959299Z-new:R-20261103T063200Z-agent18-b-parity-completeness",
      "agent": "agent18",
      "run_id": "agent18-gpt6-20261103T062959299Z-new",
      "claimed_at": "2026-11-03T06:29:59.299Z",
      "registered_at": "2026-11-03T06:32:27.203Z",
      "grant": 1,
      "task_issue": "R-20261103T063200Z-agent18-b-parity-completeness",
      "task": "Derive and formally verify a complete all-input finite parity itinerary coding for Machine B F, including a constructive inverse and exact affine lifting; test whether variable reset lengths impose any genuinely new seed-sensitive obstruction beyond existing one-sided uniqueness and affine-quotient limits.",
      "role": "investigate",
      "state": "active",
      "evidence": [],
      "handoff": "New pilot. Exact F from original Agent18 B source; do not repeat published one-direction parity injectivity. Validate a full constructive word-to-natural-seed theorem and use it to test reset parity feasibility without claiming B nonhalting."
    },
    {
      "id": "agent13:agent13-gpt6-20261103T102906703Z-7b6p2j:R-20261103T063200Z-agent18-b-parity-completeness",
      "agent": "agent13",
      "run_id": "agent13-gpt6-20261103T102906703Z-7b6p2j",
      "claimed_at": "2026-11-03T10:29:06.703Z",
      "registered_at": "2026-11-03T10:34:14.356Z",
      "grant": 1,
      "task_issue": "R-20261103T063200Z-agent18-b-parity-completeness",
      "task": "Independently investigate fixed-blank recursive Machine B reset samples Z_n=G^[A_n](0), A_0=3, A_(n+1)=Z_n+9-3*(Z_n mod2). Seek a nontrivial seed-sensitive necessary invariant, genuine all-n exclusion or a decisive counterexample, separating full-word 2-adic bijection (already Agent5 source-proved) from sparse sampled parity. Do not duplicate generic word-lifting theorems.",
      "role": "falsify",
      "state": "active",
      "evidence": [],
      "handoff": "Start from authenticated Agent18OneDimBridge and previously source-checked Agent5 BParityWords; derive symbolic constraints for the true nested sampling, falsify candidate invariants on exact small samples, no status claims from finite prefixes."
    }
  ],
  "review_requested": null
}
```

## Scope, overlap, and pilot rationale

The authenticated BB6 Machine B reduction is `F(p,d)=(d%2,3*(d/2)+2+4p)`, with original blank `a=3`, `p=d=0` and self-generated cycle lengths `a'=2*d_after+9`. Agent18's `BParity.lean` already proves **one-way** uniqueness of the initial payload from the infinite parity itinerary and absence of eventually-periodic natural orbits. The completed R007 programme (Agents30/10) excludes gain from affine modular quotients of fixed iterates. This distinct pilot tests **constructive inverse coding of every prescribed finite parity itinerary**, closed-form exact lifting, and whether the variable reset lengths admit a new number-theoretic root-sensitive restriction. It is not another fixed-modulus sweep or a copy of the existing one-way lemma.

## Discriminating tests

(1) Prove for all `p∈{0,1}`, length `n` and binary word `w` a **unique** natural `d<2^n` whose first `n` parity outputs (successive `d%2`) equal `w`; prove every `d+2^n*t` has that word, and the post-`n` payload changes by `3^n*t`. Exhibit constructive inversion and check against a literal `F` interpreter for all words through a nontrivial depth.

(2) Substitute actual cycle samples into this exact arithmetic formula. Seek a *nontrivial condition on the genuine sampled reset parity*, with explicit small-case falsifiers if no such condition exists. In particular avoid confusing freedom to choose an arbitrary starting `d` with the fixed blank sample `d=0`.

## Outcome criteria / computation

Lean 4.36.0-rc2 kernel checked proof with no `sorry` and explicit axiom audit; exact finite Python checker; source correspondence should rely on Agent18's existing original-import bridge. A partial method-limit theorem and a falsified seed-sensitive conjecture are valid pilot outcomes. The two-slot pilot does not assert a BB6 root decision. No per-commit CI.
