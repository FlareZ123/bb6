# Raw58 LF1 RLE candidate: leaf 1181

**Status: computational certificate candidate; Lean source audit pending.** This is an intermediate result, not a closed LF1 child or a Raw58 parent Cover.

## Exact residual

- Child: `LF1`
- Open-leaf index: `1181`
- Partial table: `1RB1LF_1RC0LB_0RD1RA_1LD1RE_---0RA_1LB0RF`
- Two-sided run-length abstraction: `left=(20,8,16)`, `right=(20,8,16)`

A direct reimplementation of the repository's `rlelearn.check` returns a closed non-hole relation with 16,776 joint configurations and stack automata of 3,033 / 4,307 states. The repository incidence quotient preserves the closure predicate and reduces this to 6,908 joint configurations and 2,498 / 1,870 stack states. The parameter tuple was found by extending the symmetric search beyond the existing small grid; the exact Python checker was then run independently on the candidate.

## Reproduction and source audit

The candidate is declared in `im-results/agent4-raw58/more.json` under `LF1.automata["1181"]`. The reusable automata-only path is a selector in the existing `agent10-four-hole.yml` workflow (no new workflow file):

- target: `raw58-automata`
- child: `LF1`
- automata id: `1181`
- expected theorem: `BB6.Agent4Raw58LF1Automata.M1181.never`

The generator re-enumerates the exact open-leaf source, checks its digest and the table at index 1181, constructs the finite relation, applies the incidence quotient, and emits the row-sharded Lean certificate. The workflow compiles the generated module and audits the theorem's axioms. A successful Lean run is required before describing this as source-accepted.

## Scope limit

The LF1 child still has nine other unresolved leaves. This candidate alone does not close that child, establish its complete partition, produce a Raw58 parent Cover, or alter the conditional Canonical68 upper-bound obligation.
