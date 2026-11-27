# Raw47 depth-three coverage research

Parent `1RB---_1RC---_0RD---_1LD0RC_------_------`.

## Accepted exact quotient cut

**123 open depth-three cylinders at weighted bound 10,006.** The original depth-three tree has 126 first-hole splits, 1,567 cycle closures, 120 state-introduction aliases, and 1,212 distinct canonical residuals. The exact tree cut at weighted bound 84 and its count are accepted by Lean. The current source-accepted consumer removes 1,089 residual cylinders, 282 more than accepted807.

`BB6.Agent50Raw47Accepted1089.local_sound` establishes that every machine quotient-compatible with the authentic Raw47 parent either satisfies `WeightedBound 10006 m` or is quotient-compatible with a member of the exact remaining roster. The kernel checks `remaining_count` (123), `closed_count` (1089), and `keys_eq`; all four theorems have standard axioms only.

- Accepted [run 46051657196](https://github.com/FlareZ123/bb6/actions/runs/46051657196), full proof artifact [15225945201](https://github.com/FlareZ123/bb6/actions/runs/46051657196/artifacts/15225945201), SHA256 `9e4095f6cabc1e0dd5044ad11a33f783562b5f768798a115932100f65297afef`.
- Compact exact evidence [15225510313](https://github.com/FlareZ123/bb6/actions/runs/46051657196/artifacts/15225510313), SHA256 `973d8d7d312e4125a60c9c7c42cb3ffcc21590fd1251f826f9e3d7e6e3033dd2`, includes all closed/remaining IDs and tables, source revision, root manifest, axiom audit and artifact provenance. [Remaining 123 literal tables](remaining123.txt).
- Exact original roster SHA256 `4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d`. `FastKey.lean` proves injectivity of the twelve-slot base-26 code and the kernel computes the exact remaining list. No positional correspondence is assumed.
- The previous accepted807 baseline was [46031130982](https://github.com/FlareZ123/bb6/actions/runs/46031130982), artifact 15214821612. The new composition consumes the eight completed graph runs 46031706884, 46032082092, 46032804061, 46033068244, 46033502720, 46033647191, 46038945002, 46040218912. All 282 additional intended parent Covers were accepted. The streamed merger processes source-accepted artifacts one at a time and writes a compact evidence package.

## Exact remaining proof edges

Of the 123 remaining cylinders, two now have independent complete source-accepted Covers at 10,006 (601 and 609); one has an independent complete source-accepted Cover at 143,977 (61); and the other 120 are precisely the selected middle-region parents in [46051808874](https://github.com/FlareZ123/bb6/actions/runs/46051808874). The missing edge is checked composition of these additional Covers; no complete Raw47 Cover or global representative removal is yet claimed.

**601 and 609:** previous paired job failed. Local exact enumeration found 25 and 32 open leaves. The frozen FAR5 bank closes 53 of 57; cheap run-graph closes three; exhaustive FAR6 search finds code `1010232450112` for the last leaf `1RB0LE_1RC1LA_0RD1LB_1LD0RC_1LF---_1RD0LB`. [Raw47FAR609.lean](Raw47FAR609.lean) proves nonhalting for every compatible completion; original-source local Lean RC2 checked standard axioms. The exact literal-keyed certificate is included in the generator. Both `BB6.Agent50.Raw47D3G601.all_quotient` and `BB6.Agent50.Raw47D3G609.all_quotient` passed [source CI 46052244263](https://github.com/FlareZ123/bb6/actions/runs/46052244263), standard axioms only, zero partial children. Artifacts 15225405955 (601) and 15224842816 (609).

**61:** The exact U61 partial roster has one leaf `1RB1LA_1RC0LF_0RD0LE_1LD0RC_0LA0RB_---1LB`, key 25578468639170103. Its first undefined transition occurs after 143975 moves. Generic [CheckedSweepTrace.lean](CheckedSweepTrace.lean) proves exact finite command traces; the generated 2741-command trace uses 69 chunks. Source CI [46033320715](https://github.com/FlareZ123/bb6/actions/runs/46033320715) accepted exact weighted attainment 143977 and the parent theorem `BB6.Agent50Raw47Late61Parent.all_quotient`. See [Late61.md](Late61.md). This proof cannot enter the 10,006 cut. Lift only after composing all other parent Covers.

**Final adapter:** [Raw47CoverEmpty.lean](Raw47CoverEmpty.lean), locally checked with standard axioms, turns an exact zero residual list into a quotient theorem and `Cover (WeightedBound B)` at the same bound, and proves monotonicity to larger B. The lifted workflow emits `Raw47Complete` only if it reaches the checked empty roster; the final template is prospective until original-source CI passes.

**Next action:** once the middle sweep completes, merge its successful artifacts and 46052244263 against accepted1089. If any U partial survives, solve its exact leaves rather than rescan the accepted bank. If the result is accepted1211, lift using late61 run 46033320715; the final Cover workflow requires exact zero residuals. Communicate the accepted whole-parent theorem and artifact to the global consumer.

## Historical accepted cuts and methods

Accepted807 (405 open) followed accepted766, 729, 702, 678, 168, 120, and 108. All 674 pure FAR parents and the 23 pump/counter parents were consumed before accepted702; the subsequent exact graph batches add more parent Covers. The cap-10,000 scan produced 45,817 open leaves; FAR through five states closes 43,659 candidates, n-grams widths 2–10 close 1,498 (544 overlap). With the original hard-leaf theorems this left 1,192 candidate leaves across 382 parents. Agent12 run-graph search and Agent2 carry proofs discharge the rest; only exact parent audits and source-accepted composition count as proof. See [PumpCertificates.md](PumpCertificates.md), [CounterCertificates.md](CounterCertificates.md), and [Late61.md](Late61.md).

## Historical experiments

The verified depth-2 Raw47 cut leaves 114 five-hole residuals, none certified by FAR through six states. This experiment increases the local split depth from 2 to 3 while keeping the same 1,000-step simulation cap and 32-frame cycle lookback. It then runs the FAR5 bank over every resulting open residual.

Reproduce with `.github/workflows/agent50-raw47-depth3.yml` or `bash im-results/agent50-raw47-depth3/run_depth3.sh [output-directory]`.

The purpose is to expose one more undefined transition per surviving branch. Open leaves may therefore have four or five holes depending on whether a branch reaches the simulation cap before the next split. The output records the exact tree, open list, FAR5 candidates, and hole-count distribution.

This is intermediate computational evidence. A candidate bank is not a proof until converted into Lean FAR certificates and checked; a deeper tree does not by itself reduce the global Canonical64 obligation count.
## FAR6 preloader correction

The first FAR6 attempt was invalid: the C++ preloader expects one bare code token per line, but the initial runner passed the FAR5 `id code` output. It therefore parsed IDs as automaton codes and falsely reported all 1212 leaves solved in 0.00 seconds. Those files are explicitly preserved with an `-invalid` suffix. The corrected runner extracts only the second column of the FAR5 bank, validates the ten bare codes, and reruns FAR6. Only the corrected run may be cited.


The prior `raw47-depth3-far6.txt` is invalid (contains numeric IDs treated as codes). Do not use it as evidence.
