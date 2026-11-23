# Machine C low first-stop inverse chains

**Status: source-proof draft; unchanged-source CI is pending.** Do not treat either family as accepted until the manual Agent 21 workflow completes successfully and its axiom report is free of `sorryAx`.

## Claim under verification

For the original Machine C section transition `BB6.Agent46.secNext`, starting at `(5,1)`, let a low first-stop target be `(1,k)` with
[
k+3m+4=2^{2m+3}.
]
The Lean module `Low1091Source.lean` aims to prove all-time nonreachability for both progressions:

- (mequiv1091pmod{4096});
- (mequiv12355pmod{16384}).

The formal theorems are `first_stop_m1091_mod4096` and `first_stop_m12355_mod16384`. Each excludes the target for every section-run time, not merely within a bounded simulation.

## Shared exact inverse chain

Writing (k=1024q+819), the first five forced source inversions are valid for every (qinmathbb N):
[
egin{aligned}
(1,1024q+819)
&leftarrow(512q+408,768q+612)\
&leftarrow(1280q+1018,384q+305)\
&leftarrow(832q+659,608q+481)\
&leftarrow(720q+568,664q+523)\
&leftarrow(692q+543,678q+532).
end{aligned}
]
The arrows point from a target to its uniquely classified immediate source parent. The classifications use the complete original-source inverse predicate, the even/even affine classification, and the mixed-parity valuation-two classification.

The last state has even right coordinate. Whenever its coordinate sum is neither (0) nor (7pmod8), the source-certified even-right reachability theorem forces its direct predecessor ((x+y-2,(y-2)/2)).

### Cylinder (qequiv0pmod4)

The stopping equation for (m=4096r+1091) gives
[
q+12r+4=2^{2m-7},
]
hence (qequiv0pmod4). One direct even-right reduction gives
[
(1370q+1073,339q+265).
]
Its right coordinate is odd and its coordinate sum is (2pmod4).

### Cylinder (qequiv11pmod{16})

For (m=16384r+12355), the stopping equation gives
[
q+48r+37=2^{2m-7},
]
hence (qequiv11pmod{16}). With (q=16v+11), three direct even-right reductions end at
[
(30056v+22129,1356v+997),
]
again with odd right coordinate and coordinate sum (2pmod4).

The existing all-time blank-section image theorem `BB6Agent38.blank_section_mod4` forbids such a state except for the seed `(5,1)); both terminal states have right coordinate at least (5), so neither is the seed.

## Relation to the maintained low sieve

Both progressions have (mequiv67pmod{1024}), (mequiv3pmod{16}), and (m
otequiv0pmod{128}). They therefore pass the currently published `jointLowAllowed`, `Agent11Joint.lowAllowed`, and `lowAllowedValSixFull` residue restrictions. The new exclusions are intended to refine, not replace, the unbounded low-parameter existential in `ValSixJointFull.lean`.

This is not a decision of the residual low existential, the high existential, Machine C halting, or BB(6).

## Files and verification

- `Low1091Source.lean`: complete Lean source proof and axiom reports.
- `../../.github/workflows/agent21-low1875-source.yml`: focused manual source workflow, compiling the unchanged section/bounce dependencies and this module.
- CI run currently pending: [run 45140347758](https://github.com/FlareZ123/bb6/actions/runs/45140347758).

## Next useful work

1. After CI acceptance, integrate these exclusions into a strengthened low predicate alongside `lowAllowedValSixFull`, preserving the existing exact joint halting equivalence.
2. Formalize the next direct-parent cylinder (qequiv39pmod{64}), which the arithmetic chain maps to (mequiv8259pmod{65536}); do not cite it until its unchanged-source Lean proof passes.
3. Continue the 2-adic direct-parent tree only where each reduction is justified by the original-source even-right theorem; exceptional sum residues (0,7pmod8) require separate inverse analysis.
