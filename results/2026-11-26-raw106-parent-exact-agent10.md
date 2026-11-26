# Raw106 exact weighted maximum: 253

**Theorem.** For the exact partial table `1RB---_1RC1RF_0RD---_1LD1RE_---0LB_------` (five holes), every compatible machine satisfies `WeightedBound 253`, and 253 is the least such bound. The completion `1RBHHH_1RC1RF_0RD1RA_1LD1RE_1RC0LB_1LF0LE` executes exactly 252 ordinary transitions before the undefined A1 query, and admits delay 0. Here the convention counts the final halting query and incoming blank delay.

The sparse partition covers all 25^5 = 9,765,625 physical completions: 1,735 split nodes including root, 32,444 side-cycle leaves, 6,155 last-hole leaves, 1,305 FAR leaves and two universally quantified symbolic growth leaves. The original enumeration's open list SHA-256 is `6144aa5292cd37d18359fe9209293e30c795a110468e65e5a1ab8332d58b5312`. Candidate search is untrusted: every partition edge and terminal proof was checked by the original source Lean checker.

## Acceptance and reproducibility

On 26 November 2026, the **complete original-source closure** of 78 Lean modules from Agent27's [source-export run 45746231446](https://github.com/FlareZ123/bb6/actions/runs/45746231446) (artifact 15082864386) compiled locally, without mocked imports or native_decide, using Lean 4.36.0-rc2. The bundle's original source revision is `d4f8af6c95aa037f2a1a195301471bdacb1c78c2`; ZIP SHA-256 `14af9c45666a811679cdf36f03a740e7252d15483e0994b91600e901a2467692`, manifest SHA-256 `c1677409b11d0149b124d8c1f1d99ad79fe8ebf1e28dc65bda5611119c548cec`. Each of the 78 module SHA-256 values was checked against the manifest before compilation, and all project imports were present. No earlier interrupted CI run is used as evidence of acceptance.

Reproduce via the pinned source-only export script [export.py](../im-results/agent27-retained-parent-source/export.py), with target raw106 at the indicated revision; the original generator and witnesses are in [agent10-tnf-multipump](../im-results/agent10-tnf-multipump/README.md). Compile the source manifest's modules in topological order (all 78 exited 0 locally); then compile [Raw106Attainment.lean](../im-results/agent10-tnf-multipump/Raw106Attainment.lean) and [Raw106ParentCover.lean](../im-results/agent10-tnf-multipump/Raw106ParentCover.lean) in the same closure, in that order. The source artifact may expire; the pinned generator/export is the durable regeneration route. The local result is not a new hosted CI acceptance.

The kernel output for the parent:
```
'BB6.Agent10Raw106.tree106_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent10Raw106.all106' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent10Raw106.parent_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent10Raw106.literal_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'BB6.Agent10Raw106.exact_weighted_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The lower witness, compatibility, literal-parent identity and zero delay were separately compiled from the exact source. Their axiom profiles are subsets of the same standard axioms.

**Scope:** this is an unconditional finite-cylinder decision, not a global BB(6) upper bound. Exact membership and integration in the current canonical residual consumer are separate proof obligations. Agent31 is coordinating that consumer.
