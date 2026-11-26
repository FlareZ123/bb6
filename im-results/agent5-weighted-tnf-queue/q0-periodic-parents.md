# Complete computational candidates for q0 active roots 55–58

The 1,000,000-fuel q0 source checkpoint contains 156 active parents and one held parent. These four parents have A0=1RB, A1=1RD, B0=1RC, C0=0LA, D0=1LA, D1 in {0LE,0RE,1LE,1RE}; six slots remain unspecified. Exact checkpoint identities are enforced in the generator.

| index | D1 | nodes | side | coarse | splits | short last | initially open | extra FAR | extended last | weighted ceiling |
|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 55 | 0LE | 601969 | 430255 | 17102 | 25082 | 129287 | 243 | 242 | 1 | 1697 |
| 56 | 0RE | 360361 | 251964 | 8392 | 15015 | 84919 | 71 | 69 | 2 | 12333 |
| 57 | 1LE | 873793 | 606353 | 34384 | 36408 | 195980 | 668 | 667 | 1 | 1547 |
| 58 | 1RE | 405841 | 281793 | 12970 | 16910 | 93983 | 185 | 185 | 0 | 656 |

Each split is a first queried undefined slot; the halt alternative is covered by source_first_hole_split, every one of 24 ordinary completions is a child. Last-hole witness uses first query n, allowing at most six extra weighted steps. New FAR uses (a) maximal alternating runs, (b) runs of lag-p XOR discrepancy, (c) fixed-width aligned block runs. 59 alternating, 16 lag, 4 aligned-block certificates cover all previously difficult leaves. Every generated certificate is independently checked for original-direction closure and totalized MITM. The aligned-block certificates are for four root57 leaves, with 1022, 3344, 1767, 1851 reachable rows (widths 3,4,5,5).

Reproduce from this directory:
`node q0-periodic-parent.cjs 58` (JSON manifest only);
`node q0-direct-parent.cjs 58 /tmp/Agent5Q0AutoData.v` (source verifier shards; original-source workflow existing enumerate62-direct-parent target).

The normalized run automata start at JSON [] instead of historical empty-string map key (which creates duplicate blank state). Historical bank remains unchanged; explicit certificates are generated from normalized bank, not interpreted as old bank indices.

**Status:** all four computational candidates complete; no parent accepted until source Coq or Lean coverage assembly passes. Root56 exact recurrence and its weighted bridge have been compiled locally. The 4GB local memory limit prevents a monolithic tree build; per-shard proof generation avoids monolithic proof terms.
