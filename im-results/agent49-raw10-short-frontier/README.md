# Raw10 shallow first-hole frontier (Agent 49)

Research checkpoint: candidate generation, not yet source-kernel accepted.

Search starts with A0=1RB, B0=1LC, branches at actual first unknown query on all 25 concrete choices (including assigned halt), for at most three assignments. Existing 66 encoded cylinders are skipped only when they subsume the entire node. Stop at an explicit halt or a witnessed half-line recurrence, with a 160-step discovery cap and period <=128. Other nodes are retained. Discovery uses the existing Agent31/50 recurrence method; no new nonhalting criterion is asserted.

The full C1=halt cylinder has 25^9 completions: two ordinary transitions then the halt attempt, weighted bound 8. A1 is unrestricted. This subsumes the earlier four-fixed-row candidate.

```json
{
  "depth": 3,
  "limit": 160,
  "oldRows": 66,
  "oldBoxes": 34,
  "oldResidual": "90890091604975",
  "newLeaves": 3400,
  "halt": 463,
  "cycle": 2937,
  "open": 7700,
  "skipped": 13,
  "rawLeafMass": "43896484375000",
  "newlyCovered": "43896484375000",
  "remaining": "46993607229975",
  "maxHalt": 8,
  "maxCycle": 21
}
```

Exact integer counts from disjoint first-hole branching and intersection with the previous 34 residual boxes. They are diagnostics, not kernel theorems. Old held FAR compatibility remains conditional. Newly covered mass excludes any overlap with the 66 old cylinders, including held. The 3400 candidate leaves are independently checkable through the existing finite halt and half-line recurrence source lemmas. The table decoder explicitly distinguishes wildcard from fixed halt. Raw10ShortBridge supplies the combined conditional cover, keeping every unresolved rectangle and the held bridge obligation. None of these data imply global BB6 exactness.

Reproduce: `node generate.cjs ../../agent49-box-complement/Raw10Encoded.lean` from repository root with the proper input path (default uses the root-relative path; simplest run `node im-results/agent49-raw10-short-frontier/generate.cjs`). The JSON output includes all candidate and open cylinders. The generator itself is outside the trust boundary. Lean data are chunked for kernel reduction. No new CI workflow is added; integrate into an existing source closure audit. Source compilation not performed in this invocation because local git DNS fails; Lean itself is available.
