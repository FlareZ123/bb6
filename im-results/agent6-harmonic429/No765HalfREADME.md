# BB429 four entire 765-sector halting lifts eliminated modulo 8192

**2026-11-04, Agent 6.** Intermediate source-shaped Lean proof; do not promote to the publishable `results/` collection until independent original-source integration and external novelty assessment.

## Exact statement

For the genuine accelerated blank orbit `BB429.run n (0,0) = some (a,b)`, whenever `b+1 = 2*a` (the exact unique halting gateway), the counter `a` cannot be congruent to **2813, 3837, 4861 or 5885 modulo 8192**. This holds for **all natural macro times and all natural counter magnitudes**. [Lean module](BB429NewResidue.lean), theorem `BB429NewResidue.blank_halt_not_four_residues_mod8192`.

The four excluded congruences are four of the eight lifts of the formerly surviving `a≡765 (mod 1024)` class. The remaining four lifts in this cylinder are `765, 1789, 6909, 7933 (mod 8192)`. This is a necessary-terminal-gate refinement on a single unresolved machine. It neither proves nor disproves that the blank orbit halts.

## Proof mechanism

The source accelerator `BB429.next` has only two incoming branch types for any target with **odd first counter at least 13**:

- its first branch, with `a=2*x+3` and `y=b+a`;
- an odd non-first branch, necessarily `b%4=2`, with `4*x+26=4*a+b` and `2*y=b+4`.

The two alternatives are exhaustively extracted directly from `BB429.next` in `odd_inverse`; there are no hypotheses about being on the blank orbit in this lemma.

Set `a=8192*q+1024*r+765` with `r∈{2,3,4,5}`, `b=2*a-1`. The all-time blank-root invariant `BB429Mod8.Allowed` is already proved in `BB429Mod8.lean`. Reverse the exact transition graph from that terminal line. Each path ending after a finite sequence of predecessors is contradicted by `Allowed`; the proof explores all first/non-first alternatives at branch splits. Maximal branch depth is 12 macro-predecessor steps, uniformly in `q`.

The two deepest exceptional leaves need an even-target inverse lemma: if `a≥6` is even and `BB429.next(x,y)=some(a,b)`, necessarily `4*x+14=4*a+b`, `2*y=b`, `b%4=2`. This is independently exhausted from the original branch definition as `even_inverse`. The parent in each exceptional branch has positive even first counter but second counter congruent to 3 modulo 4, which the already established `Allowed` invariant excludes.

The source file contains a separate theorem for each intermediate affine family, retaining the original blank-reachability hypothesis throughout the inverse tree and proving the final nonreachability for `q` universally. The proof has no hardcoded finite simulation horizon.

## Verification status and boundaries

Local Lean **4.36.0-rc2** compiled the entire new file without errors and `#print axioms` showed only `propext`, `Classical.choice`, `Quot.sound`, and the existing `BB429Mod8.all_blank_returns_allowed` import in a temporary test facade. The test facade copied **exactly** the checked-in `BB429.next` definition and the `BB429Mod8.Allowed` predicate, and declared **only pre-existing proven source theorem signatures as local axioms**. Thus this is a kernel check of the new proof logic relative to authenticated prior lemmas, **not** a full unchanged-import compilation.

The prior `BB429Mod8.all_blank_returns_allowed` is genuine source-checked in previous pinned original-Cryptids runs, and the complete authentic source bridge for the predecessor 44-class theorem succeeded in [run 41869801195](https://github.com/FlareZ123/bb6/actions/runs/41869801195). The generic [shared pinned source audit](https://github.com/FlareZ123/bb6/actions/workflows/shared-cryptids-source-audit.yml) was dispatched on November 4 as run [41877217781](https://github.com/FlareZ123/bb6/actions/runs/41877217781), but captured an **earlier two-residue version** of `BB429NewResidue.lean`; it does not validate this four-residue revision until a separately dispatched run completes at the corresponding revision. The 44-class previous source audit cannot be cited as checking the new four-class theorem. Verify and update this status before using source-pinned claims.

No external-priority novelty comparison has been completed; neighboring researchers may independently derive overlapping modular cuts. Existing Agent 1 proofs for 1661 and 893 modulo2048 concern **different cylinders** and should not be counted as overlapping this four-lift family.

## Next direction

The surviving lifts of the 765 cylinder, especially `r∈{0,1,6,7}`, present substantially deeper and 2-adically branching reverse families. A finite sample that prunes them is insufficient for a universal exclusion. Target an all-natural inverse certificate or a last-real-nonfirst-seed invariant for one whole remaining lift. Do not infer a universal #429 nonhalting result from these modular conditions.
