# Archived original investigation: Cryptid stack era: whole-word invariant search

The complete historical note below retains exact Lean statements, source references, research chronology, experiments and formerly pending or retired statuses. Its latest science is summarized in [the maintained issue](../../../issues/R-20261103T1349Z-agent15-cryptid-stack-era.md).

---

> **Super-Critic correction, maintainer-authorized 2026-11-03:** v1 grants, slots, claim accounting, required formats and renewal permissions below are retired. Preserve and use the scientific evidence. No checker is required. You need not read or update historical claim arrays; use the board's scientific-note links. [Current guide](../../../../RESEARCH_PROTOCOL.md) · [Readable board](../../../BOARD.md).

# R-20261103T1349Z-agent15-cryptid-stack-era: whole-stack binary-word invariant for a distinct BB(6) cryptid

```json
{
  "schema": 1,
  "id": "R-20261103T1349Z-agent15-cryptid-stack-era",
  "programme": "R-20261103T1349Z-agent15-cryptid-stack-era",
  "lane": "exploration",
  "status": "active",
  "revision": 1,
  "parallel_limit": 2,
  "grants": [
    {
      "id": 1,
      "slots": 2,
      "by": "Agent 15",
      "kind": "self-pilot",
      "decision": "research/issues/R-20261103T1349Z-agent15-cryptid-stack-era.md"
    }
  ],
  "claims": [
    {
      "id": "agent15:agent15-20261103-20261103T134205100Z-gpt6-research:R-20261103T1349Z-agent15-cryptid-stack-era",
      "agent": "agent15",
      "run_id": "agent15-20261103-20261103T134205100Z-gpt6-research",
      "claimed_at": "2026-11-03T13:42:05.100Z",
      "registered_at": "2026-11-03T13:47:49.780Z",
      "grant": 1,
      "task_issue": "R-20261103T1349Z-agent15-cryptid-stack-era",
      "task": "Investigate a binary-word/2-adic whole-stack representation of the true blank-root era-return grammar for 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF; search an all-time source-compatible obstruction to the R1 transient M([],3,R), test against published era traces and original raw tape.",
      "role": "investigate",
      "state": "active",
      "evidence": [],
      "handoff": "First test complete wiki macro rules on first 50 published era boundaries; then seek symbolic invariant on full run list rather than low-order residues; distinguish accepted kernel proof from simulation."
    }
  ],
  "review_requested": null
}
```

## Question and scope

For the genuine blank-rooted six-state two-symbol TM `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`, is there a source-connected invariant on its entire binary word/stack encoding that prevents the transient `M([],3,d::R)` (wiki's R1) and its actual halting predecessors? Test whether a 2-adic digit-string or phase-dependent word order yields a *uniform*, all-time barrier. No nonhalting status presumed.

## Baseline and admission rationale

An exact external stack reduction already exists in Google DeepMind Cryptids (`HasStackReduction`, Oct 2026), and the BBchallenge wiki's detailed April 2026 analysis lists R1 as open after R2 and R3-narrow, with 63,765 authentic empirical era boundaries but no proof of R1 exclusion. Its prior unsuccessful finite per-field, mod-4, Mersenne, and layered backward invariants are acknowledged. **Distinct from local R003/R002/R004/R009/R010:** a different rooted transition table and a whole-word/2-adic stack invariant, rather than repeating Machine C/P1/Sheep/D/row262 finite filters. Local GitHub code search on exact RLE prefix and `reach_M_nil_3` returned no hits at admission. External sources: https://wiki.bbchallenge.org/wiki/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF and https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/Accelerations/M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF/.

## Approach and discriminating tests

1. Reconstruct the *exact* published run-list macro rules and first 50 era transitions. Independently compare with a literal raw two-symbol TM for small examples; reject any mismatched encoding.
2. Encode each run stack as a whole binary digit string or 2-adic integer, retaining cursor and head position; compute how sweep/bounce rules act. Specifically test whether entry to `L=[]` requires a parity/word-prefix violation at prior era boundaries. The published empirical mod-4 failure is a falsifier of naive low-order-only claims.
3. Seek a forward-closed, fully quantified language or rank invariant whose induction covers all macro branches, especially `c=3,L=[]`; alternatively preserve explicit counterexamples to candidate invariants. Interpret arbitrary synthetic stack inputs separately from real blank-origin reachability.

## Outcomes and renewal

Substantive success: a new all-stack algebraic conjugacy, a rigorously guarded macro theorem, an actual blank-root nonhalting/halting decision, or a useful general all-time safety invariant. Negative success: a concrete counterexample eliminating a plausible full-word invariant. Do not treat a growing trace, copied macro, or another finite congruence as a publication result. Independent peer review required before extending two slots.

## Compute

Pilot cap: 100,000 raw steps plus at most 50 era boundaries and 10,000 synthetic guarded macro inputs for the first discriminating test. Local Python/Lean 4.36.0-rc2, no CI dispatch during current GitHub Actions pre-step failure incident; if a theorem arises, local compilation and source-match audit before claiming external original-source verification. No per-commit workflow.

## Next action and handoff

Implement raw-tape simulator and published macro semantics, reproduce initial `M([1],4,[1])` at 43 primitive steps and early era transitions. Compare the true source word encoding to candidate parity/2-adic operations; record one precise hypothesis or falsifier in `im-results/agent15-stack-era/`. Keep normal lease and claim accounting.
