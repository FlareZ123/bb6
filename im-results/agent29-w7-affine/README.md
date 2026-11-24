# Independent affine execution of W7-2

**Current result (24 November 2026):** independent computer-assisted reproduction of both entire blank-root nonhalting arguments. The source-table exact Python computations are now backed by a kernel-proved Lean certificate checker and closed native-checked nonhalting theorems; the remaining non-kernel trust is the six generated native_decide facts. Neither root is claimed to be a newly discovered community holdout; both were deleted from the historical October roster. No universal BB(6) bound follows.

Literal table: `1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD`. Historical row 146 is blank A; [Agent29's conjugacy](../agent29-roster-six-audit/Row146Conjugacy.lean) identifies row 411 with the mirrored/renamed blank D. Prior [Agent3 physical-block proof](../agent3-w7-physical-block/README.md) proves seven sweep identities. The targets come from [Dennis Koshta's informal proof](https://github.com/DennisKoshta/denniskoshta-portfolio/blob/b48bd32fab8b476135d47ffa4e5f9bfb9a80d8c7/public/busy-beaver/machines/1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD/proof.md.html), not a newly inferred invariant. Our implementation is independent of his engine, which was not present in the archived scripts directory.

## Exact endpoints

Outside the displayed finite word all cells are zero; a four-bit word is repeated by its exponent. `<A` reads the last bit of the left block; `C>` reads the first bit of the right block.

* N(Y) = 0001 1011^Y <A 0001^28 0011 0000 1000.
* Q(W) = 0011 1101 F> 1010 0010^W 0000 0010^28 0000 1000 0100.
* D(X,Y2,Y1) = 1101^17 1111 0111^X 1101^Y2 1111 0111^Y1 C>.

The independent executor reached, and the recursive replay with exact shape checks accepted, these endpoints:

| Start | End | Top-level accelerated operations | Distinct dependency rules rechecked |
|---|---|---:|---:|
| blank A | N(508932094) | 486624 | 18995 |
| N(22+m) | N(38626190+262144m) | 138704 | 5522 |
| Q(14+m) | Q(38101896+262144m) | 138541 | 5534 |
| D(100+x,130+b,30+a) | D(454337500+1048576x,10+b,6+a) | 413778 | 19608 |
| D(349479900+1048576z,5759218639205926131,13) | Q(23036877419765819664+8589934592z) | 256274 | 10322 |

Each parameter is an independent natural number. The counts are accelerated operations, not primitive TM scores. The first two lines imply blank-A nonhalting: the successor of every N(Y), Y >= 22, is N(262144Y+32859022), again in the same domain, by a positive finite run. Iteration gives arbitrarily long defined primitive runs. The second root follows from its independently replayed blank-D entry and the D iteration below.

## Soundness argument

The code represents the tape in four-cell blocks by two lists of runs, nearest block first, with implicit zero blocks beyond the lists. The head's direction bit identifies its actual cell on the neighboring block. Every block step runs the literal table until leaving that block, rejecting a halt or an internal repeated finite state. The only sweep acceleration is for unchanged state and exit direction; repeating an identical input word then has exactly the effect of iterating that same local run, by induction on its positive repetition count. Exit direction determines which list receives the rewritten block; merging runs and erasing far zero blocks preserves the tape exactly. Translation of the entire tape is irrelevant to halting, since the literal machine is translation invariant.

Counts are affine forms in independent natural variables. A coefficientwise nonnegative comparison is sufficient for all valuations; positive counts additionally require positive constant term. A pop either removes an identically zero remainder or leaves a provably positive remainder; ambiguous cases fail. Quotients are accepted only when all nonconstant coefficients are divisible by the positive divisor. Thus coefficientwise exact affine execution is a universal statement, not extrapolation from samples.

A difference rule has a fixed tape shape, fixed counts on some slots, lower thresholds on others, a vector of constant increments, and a nonempty earlier trace. For proof, replace every free slot by its own independent variable plus its threshold and replay that trace. Accept only if the entire output shape and every affine coefficient match the claimed translation. Dependencies are previously proved rules; recursive replay checks acyclicity and all actual application shapes. If a rule has negative increments, its safe repeat count is the minimum over negative slots of floor((count-threshold)/(-increment))+1. The chosen minimum must dominate no other candidate for every valuation; all earlier iterations meet the threshold, fixed counts do not change, and every final run remains positive. Induction on the repeat count proves the accelerated effect. Induction on the acyclic dependency DAG proves every accepted trace is a composition of positive literal-machine runs.

The replay uses shared primitive and affine semantics with the discovery engine, but does not trust the latter's history/heuristic or sampled outcomes. The independent Lean formalization below implements and proves the semantics separately from the Python discovery code. The displayed arithmetic endpoints were computed before explicit shape guards were added to the discovery engine; all five used proof DAGs were subsequently replayed with mandatory shape guards and accepted. The stored script includes guards in both discovery and replay. Reproduce using `python3 affine_replay.py N A Q D E` (or individual case names), then compare endpoints; the guarded discovery can choose a different valid trace. The script deliberately fails if an endpoint is not found within its finite discovery budget; the proof itself has no extrapolation cutoff.

## Blank-D root: complete opening, exhaustion, and nonhalting

The separate memory-bounded [stream generator and replay](stream_entry.py) reached exactly

    D(70691118354036414594808423388,10456559309013950571,939468133961604901)

from blank D, in 6,160,484 top-level accelerated operations. It emitted 69,021 difference-rule definitions in topological order, with a gzip JSONL certificate of 1,941,761 bytes. A separate sequential replay of the emitted certificate accepted all 69,021 rules, all 6,160,484 operations, and the exact endpoint. The opening executable and replay share the same primitive and affine semantics as the first five traces.

Set X0=70691118354036414594808423388, Y20=10456559309013950571, Y10=939468133961604901. The independently checked universal D-cycle implies that for X>=100, Y2>=130, Y1>=30,

    D(X,Y2,Y1) ->+ D(1048576X+349479900,Y2-120,Y1-24).

Take n=39144505581733537. Straight integer arithmetic gives Y10-24n=13 and Y20-120n=5759218639205926131. Before the last application the two counters are 37 and 5759218639205926251, so every application satisfies the lower thresholds; X increases and remains >=100. By induction the last X has form 1048576z+349479900 for a natural z. We need never expand that enormous integer.

The independently checked exhaustion transition from the table above gives Q(23036877419765819664+8589934592z). Its parameter exceeds 14. The universal Q-cycle then stays forever in Q with a strictly increasing parameter, and each cycle takes a positive finite number of raw steps. Thus blank D cannot halt. The existing exact row411 conjugacy transfers this result to historical row411. Both roots now have complete independently reproduced computer-assisted nonhalting arguments.

Reproduce the long opening with:

    python3 stream_entry.py discover w7-D-entry.jsonl.gz
    python3 stream_entry.py verify w7-D-entry.jsonl.gz

The first local run took about 215 seconds; the second independently replayed the stream. No code from the original external engine was used. These are intermediate findings pending formal verification; the original external argument already asserted both outcomes, and this work does not establish a new community roster count or solve BB(6).

## Formalization route

A local Lean 4.36.0-rc2 development now proves the literal source block evaluator sound in arbitrary ambient tape; stack-to-raw-tape transfer, all-length sweep, affine arithmetic, and symbolic ordinary execution are also accepted. The difference-rule repeat checker and full trace acceptance remain to be integrated. Preserve these intermediate findings here until the source-anchored end-to-end theorem is established.

## Lean formal certificate checker

Local Lean **4.36.0-rc2** compiled the exact original Row146Conjugacy dependency and the full checker. The source is preserved in three byte-verified archives, containing ordinary editable Lean source (no generated binaries): [physical-source.tar.gz](physical-source.tar.gz), [affine-source.tar.gz](affine-source.tar.gz), [checker-source.tar.gz](checker-source.tar.gz). This packaging is solely for transferring the locally checked source through the repository connector.

* W7Local/W7Stack/W7Sweep: raw literal-table block execution, arbitrary ambient tape, physical stack semantics, positive finite run composition and unbounded sweeps.
* W7Affine/W7Symbolic: exact affine count evaluation, safe symbolic RLE operations, and ordinary-step soundness. W7Table proves its entire 192-entry executable block table equal to the source evaluator by kernel reduction, with no axioms.
* W7Difference: arbitrary-environment seed/slot alignment, safe repeat-count check (first and last iteration bounds suffice), proof of every intermediate iteration, and soundness of affine rule application.
* W7Checker/W7Path/W7Text: acyclic rule DAG and exact symbolic endpoint checker. `W7.check_sound`, `W7.checkPath_sound`, `W7.checkText_sound` depend only on propext, Classical.choice, Quot.sound.
* W7Roots: six universal Reach endpoints suffice for actual row146 and conjugate row411 nonhalting; the enormous D iteration is handled by induction without expanding X. Both conditional nonhalting theorems have only standard foundational axioms.
* [W7Native.lean](W7Native.lean): closed historical146_never and historical411_never, both successfully compiled locally. **They are native-checked, not kernel-only**: their printed axiom profiles contain the six generated certA/certN/certQ/certDentry/certD/certE native_decide axioms, in addition to the standard three foundational axioms. No sorryAx or user-postulated mathematical axioms. The conditional proof and checker correctness are kernel-checked.

Executable Lean replay independently accepted the six concrete certificates:

| Case | JSONL records | Top-level accelerated operations | Accepted rule definitions |
|---|---:|---:|---:|
| N | 5661 | 138704 | 5522 |
| A | 19482 | 486624 | 18995 |
| Q | 5673 | 138541 | 5534 |
| D | 20022 | 413778 | 19608 |
| E | 10579 | 256274 | 10322 |
| Dentry | 775756 | 6160484 | 69021 |

The exact symbolic endpoints are those above, independent of discovery implementation and all natural-variable assignments. The small source files are archived without certificates or compiled objects; [export_certs.py](export_certs.py) regenerates certificate input from the Python engine. Different valid discovery paths are admissible if the Lean checker accepts them. To reproduce from this directory with the specified Lean on PATH, run `bash build_lean.sh /tmp/w7-build` for the soundness modules, or `W7_EXPORT=1 W7_CHECK=1 bash build_lean.sh /tmp/w7-build` to regenerate, replay and close both theorems. Use an absolute source path for the file containing include_str, as the build script does. The exporter is a convenience wrapper around the same discovery and trace format; the exact local certificates used in this run were generated and replayed directly before the wrapper was added.

Archive Git blob identities (identical to the local binary archives):
- physical-source: dba412b40784a444c288a9c469952b8d3a165912
- affine-source: 13eec0e3568247b0d8bc0b58b2fc4845ca1dd508
- checker-source: 1246dfb16c2a832013e72333a20434f9ec7a4024

This is a formalized independent computer-assisted proof of two historically resolved-by-informal-argument roots. It belongs in im-results while native trust remains and until the research board assesses the result. It does not reduce the live community holdout count by two or prove a universal BB(6) upper bound.
