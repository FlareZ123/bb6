# BB429 q0 branch-10 notes

- [Finite inverse tree for the concrete (n,d)=(23,7) seed](../agent1-429-q0-23-7-inverse-tree.md)
- [Unbounded candidate FSFE inverse block and 2-adic depth](./FSFE-2adic-block.md)
- [Residue-level q0 coverage map](./Q0ResidueCoverage.md)

The residue map currently records ten full mod-16 exclusions plus nine additional mod-64 cylinders, for 49/64 paper-level residue coverage. These derivations combine Agent 6's six odd sectors with Agent 1's even-sector inverse refinements. The combined claim is not yet Lean-compiled; see the evidence boundary in the note.


## Additional parameterized branch reductions (Agent 1, 2026-11-18)

- [FSFE valuation tail](./FSFE-valuation-tail.md): exact F,S,F,E block in w=b-a-8; distinguishes syntactic blocks from root-compatible completed blocks; gives the first residue analysis of the competing F sibling.
- [All-F run and split formulas](./Q0-F-run-split.md): exact F^k affine formulas, split positions k=4j+1, and the secondary valuation v2(j+4) on surviving S siblings.

These are intermediate algebraic reductions, not a nonreachability proof. The q0 inverse tree has at least two distinct valuation clocks, v2(3u+5) on the FSFE branch and v2(3u+2) on the all-F branch. The a=13 mod16 FSFE sibling is narrowed one further level to a=157 or 93 mod256. The mod-256 sibling table applies only when the second block-start w is divisible by 256; in that subcase the q0 parameter forces a=13 mod256, which is excluded. Final-block cases with lower w valuation remain open. The all-F side siblings at j=2 (mod 8) close uniformly, but the j=4 and j=6 sectors contain nested residue-dependent branches. The final residual tails also remain open. Do not infer that the full q0 family is excluded from these branch-local results.

The older 49/64 residue-coverage claim remains the current documented finite coverage; the new branch formulas do not yet establish a stronger uniform coverage theorem and have not been Lean-compiled.
