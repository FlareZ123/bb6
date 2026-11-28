# Source-proved early and late halting certificates and pristine-ray divergence in the six-state Raw34 cylinder

**Agent 40 — 28 November 2026.** Original-source Lean 4.36.0-rc2 mathematical results with standard axioms; finite physical-table volumes are independently reproducible exact integer computations. **Local classification only**: this is neither a complete Raw34 Cover nor a proof of the global six-state Busy Beaver function.

## Model and statement

Work with the *original* six-state, two-symbol blank-tape semantics, one halting action plus 24 ordinary write/direction/state actions per slot. Define the eight-free-slot physical Raw34 root

```text
1RB---_1RC---_0RD---_1LC---_------_------
```

where `---` is an arbitrary instruction, including HALT. There are exactly `25^8 = 152,587,890,625` literal full-table completions of this root. We do not quotient by state renaming.

For a partial transition table `p`, `compatible p m` means that every transition assigned in `p` is identical in the total machine `m`. The original-source predicates `HaltsAfter m n` and `NeverHalts m` concern the *authentic blank tape*, not a synthetic finite seed. `HaltsAfter m n` is `(run m n blank).isSome = true ∧ run m (n+1) blank = none`; its primitive-step score includes the final query and is `n+1`.

**Finite first-query theorem.** For every partial machine `p`, natural `n`, and compatible total `m`, whenever the original checker `finiteHaltCheck p n = true`, the full blank run satisfies `HaltsAfter m n`. A checked halt is reached before any unassigned slot, so **every** completion halts at exactly the same transition query. This is the theorem `BB6.Agent40Raw34EarlyHalters.finite_check_exact_halt` in [Raw34EarlyHaltersSound.lean](../im-results/agent40-raw34-frontier/Raw34EarlyHaltersSound.lean); a companion `short_halt_sound` gives a uniform step bound for a list of checked witnesses. The proof transfers the partial finite run to the full machine using `finitePartialRun_sound`, uses compatibility at the assigned halt slot, and supplies the two conjuncts of `HaltsAfter`. It needs **no simulator cutoff assumption** for compatible completions.

### Finite-halting results and exact physical volumes

| Source-accepted theorem or bank | Universally halting literal subcylinders | Physical completions |
| --- | ---: | ---: |
| `Agent40Raw34Halt8.all_sound`, strengthened to `Agent40Raw34EarlyHalters.all_bank8_halt` | 109, with at most 8 primitive queries | 9,970,703,125 |
| `Agent40Raw34Halt9New.all_sound`, strengthened to `Agent40Raw34EarlyHalters.all_bank9_halt` | 958 further, with at most 9 queries | 1,105,468,750 |
| `Agent40Raw34LateHalters.all_halt` | 5 depth-three cylinders, halting after 9, 11, or 12 ordinary moves | **48,828,125 new** |
| `Agent40Raw34Depth4Shard00..04.all_halt` | 535 depth-four certificates, at most 26 primitive queries | **208,984,375 new** |
| `Agent40Depth5.Raw34Depth5LargeShard000..072.all_halt` | 13,884 minimal depth-five certificates, at most 27 primitive queries | **657,187,500 new** |

The 1,067 earliest cylinders were independent previously certified witnesses. Our strengthened source interface verifies *actual halting*, necessary to combine their physical volume with an independent nonhalting bank without classifying a merely score-bounded looping machine as halted.

The three **new** late levels jointly cover `48,828,125 + 208,984,375 + 657,187,500 = 915,000,000` additional, mutually disjoint full machines, beyond the early-halting bank. In particular these are not five-minutes-of-runtime empirical halt observations.

The fifth-query minimization explains why 13,884, not 42,060, source leaves suffice. A finite first-unknown-query exploration finds 42,060 halting fifth-query assignments. Discard all preassigned entries that were **never queried** on the actual terminating run, and deduplicate. The remaining source partial tables have respectively 6, 1,018, and 12,860 cylinders with 3, 4, and 5 fixed unknown root slots. Their exact physical total is

\[
6\cdot25^5 + 1018\cdot25^4+12860\cdot25^3
  =657{,}187{,}500.
\]

Every omitted instruction is truly arbitrary, including HALT, since the finite source trace does not consult it. The first-query search is deterministic in 25 original physical action choices; its source generator and exact BigInt cardinality arithmetic are [generate_depth5_halts.mjs](../im-results/agent40-raw34-frontier/generate_depth5_halts.mjs), and the 535-sibling reproducible finite audit is [audit_depth4_late.mjs](../im-results/agent40-raw34-frontier/audit_depth4_late.mjs). The generator also explicitly checks nonoverlap among new partial tables and with older genuine-halting sources, independently of uniqueness-of-first-halt semantics. This is a **finite computational cardinality audit**, not a separately exported Lean cardinality theorem.

### Lean evidence: original source and axiom boundary

- [CI 46120451493](https://github.com/FlareZ123/bb6/actions/runs/46120451493) accepted `finite_check_exact_halt`, the 109+958 strengthened actual-halting theorems, and five newly resolved later-halting three-slot cylinders.
- [CI 46120454884](https://github.com/FlareZ123/bb6/actions/runs/46120454884) accepted all five 107-witness depth-four Lean source shards.
- [CI 46120461132](https://github.com/FlareZ123/bb6/actions/runs/46120461132) accepted all 13,884 minimally source-specified depth-five halter witnesses, generated into 73 Lean modules, checking every certificate with `decide` and exporting `all_halt`; permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- [CI 46120458177](https://github.com/FlareZ123/bb6/actions/runs/46120458177) independently source-accepted the coarser 1,024 largest (three/four-fixed-slot) depth-five cylinders, with physical volume 456,250,000. These are **part of**, not additional to, the 13,884-bank above.

All CI jobs compile the transitive closure from the original checked-in Lean sources; they reconstruct the pinned original `BB6Coverage` definitions first. The CI audits prohibit `sorryAx` and `native_decide` as theorem dependencies.

## Proven infinite rays

A complementary, genuinely *unbounded* theorem closes a family that a finite-time cutoff cannot close: after the six fixed initial transitions, the head enters a pristine right half-line in state F or E. Its blank transitions write arbitrary bits but move **right** back into the closed E/F state set; the half-line ahead stays blank. Therefore no unknown marked-cell instruction is ever read and the machine diverges forever from the authentic blank tape.

The precise finite sufficient condition is `finiteRayCheck (table code) 6 true efMask = true`, and the original theorem `finiteRayCheck_sound` implies `NeverHalts m` for *every* compatible complete table. The source proofs are:

- [Raw34FRightRay.lean](../im-results/agent40-raw34-frontier/Raw34FRightRay.lean): four two-slot F-only right-ray cylinders, `BB6.Agent40Raw34FRightRay.never`; [CI 46120574275](https://github.com/FlareZ123/bb6/actions/runs/46120574275).
- [Raw34EFRightRay.lean](../im-results/agent40-raw34-frontier/Raw34EFRightRay.lean): 32 further E/F mixed-right-ray cylinders, `BB6.Agent40Raw34EFRightRay.never`; [CI 46120631488](https://github.com/FlareZ123/bb6/actions/runs/46120631488), standard axioms only.

The gross volume of these 36 cylinders should **not** be added to previous closed-control families, which substantially overlap. Instead the exact 25-ary symbolic-cube complement audit [rank_live_nonD1RD.mjs](../im-results/agent40-raw34-frontier/rank_live_nonD1RD.mjs), run with `--include-f-ray` and compared against the preceding certificate bank, reports precisely **168,034,964 newly covered physical completions**. Both prior and extended exact totals passed [CI 46120702643](https://github.com/FlareZ123/bb6/actions/runs/46120702643). This count is a finite auditable union, not a Lean `Finset.card` proof.

A separate [F-left-ray theorem](../im-results/agent40-raw34-frontier/Raw34FLeftRay.lean) and further [F translated-side-cycle sources](../im-results/agent40-raw34-frontier/Raw34FDepth2Cycles.lean) may strengthen this portfolio; do not count their fresh contribution until their original-source CI and exact overlap audit have been examined.

## Exact physical classification frontier—and limitations

The source-linked earlier portfolio (3,087 nonhalting cylinders, ten control-closure masks, E/F odometer sources, the Agent23 D1=1RD source bank, and 1,067 actual early halters) covers **147,005,580,724** literal machines and leaves **5,582,309,901** uncovered by those particular certificates. This is the auditable [source physical union](../im-results/agent40-raw34-frontier/audit_source_physical_union.mjs); its disjointness by genuine halting versus nonhalting is semantically justified, and D1 branches are partitioned literally.

The new 915,000,000 truly halting completions and 168,034,964 *additional* nonhalting completions produce the finite union:

\[
147{,}005{,}580{,}724+915{,}000{,}000+168{,}034{,}964
  = 148{,}088{,}615{,}688;
\]
\[
25^8-148{,}088{,}615{,}688=\boxed{4{,}499{,}274{,}937}.
\]

Thus this precise source-linked portfolio currently classifies approximately **97.05%** of physical Raw34 tables. The remainder is **not known to halt or diverge** based on this portfolio; many other theoretical methods may eventually cover it. This is *not* a kernel-checked aggregate Raw34 `Cover`, nor an unconditional classification of the entire Raw34 parent, nor an upper bound on BB(6).

The [ranked live complement](../im-results/agent40-raw34-frontier/rank_live_nonD1RD.mjs) computes each 25-way `D1,C1,B1` branch with an exact symbolic-cube DAG rather than guessing which subproblems remain. The canonical global [research board](../research/BOARD.md) still lists unresolved representatives and unproved Cover hypotheses; the optimal next step is to consume these accepted all-completion theorems into the **actual complementary split tree**, then prove the genuinely difficult residual branches. A finite percentage, however large, does not substitute for universal coverage.

**Status:** exact BB(6) remains an open problem.
