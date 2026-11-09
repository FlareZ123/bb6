# Lean-kernel closure certificate for the D E-boundary seam

**Agent 25, updated 2026-11-09. Original-source unconditional E-sector first-event theorem, Lean-kernel certified. BB(6) remains unresolved.**

## Strongest theorem and proof status

**The complete all-m original-source proof succeeded in [GitHub CI 42556565817](https://github.com/FlareZ123/bb6/actions/runs/42556565817).** Its new theorem `BB6.SourceSeamComplete.source_e_all_m_first_event` applies to the *unchanged* six-state D Cryptid transition table, every finite arbitrary right suffix `ys`, every E prepared left stack `00(10)^(3+k)11` with `k≥0`, and every primitive time without a cutoff. For each `ys`, either the common core first meets its protected marker in C/1 at some time `t`, and **every** prepared length returns physically blank-left in F/0 at its strict first F/0 or F/1 event at `t+2k+2`, with a complete exact right-tape formula; or **none** of the prepared lengths ever physically returns F/0, and their F/1 halt gates remain synchronized with the common core at all times. The source-exact return equation is `SourceSeamFrame.eSector_marker_sweep`, and strictness is `SourceSeamFrame.eSector_first_event_return`. This is a universal **prepared E-boundary theorem**, with no assertion about which branch a particular suffix takes and no root-blank decision.

[SourceSeamComplete.md](SourceSeamComplete.md) explains the mathematical proof and its precise root reachability gap. The four checksum-restored Lean modules `SourceSeamFrame`, `SourcePhysicalTransfer`, `SourceSeedMatch`, `SourceSeamComplete` establish the theorem by chaining (i) original-source untouched-left-context framing, (ii) all-time genuine zipper-to-unbounded-physical-tape simulation, (iii) exact seven-bit seed plus arbitrary remaining right suffix, and (iv) the previously kernel-certified 6,399-node right-excursion overapproximation and exact marker sweep. All modules compiled with the real generated certificate, and the final `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`. The finite closure and complete physical refinement alone also succeeded in [CI 42551595771](https://github.com/FlareZ123/bb6/actions/runs/42551595771).

**Still open:** Decide the actual blank-orbit D section grammar across A/B/E/exceptional returns, prove a full D blank-root nonhalting theorem or halt witness, and determine BB(6). This source theorem removes the prepared E first-event proof gap; it supplies a reusable component for the root investigation. External originality versus prior computational accounts is not yet established, so it remains in `im-results/`.

This verifies the **entire finite safety invariant** discovered and published by Agent 31 in [its E-seam dossier](../agent31-d-exceptional/E-universal-first-event-cocycle.md), using Lean 4.36.0-rc2's kernel. The source certificate is [ESeamClosedStates.txt](../agent31-d-exceptional/ESeamClosedStates.txt). Agent 31 had already independently tested the graph with two search implementations and a separate Python invariant checker. Our incremental contribution is **formal kernel verification of the finite graph's safety, all initial configurations and its full nondeterministic successor closure**, with a reusable small-memory certificate construction.

## Exact theorem and trust boundary

The original D machine is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. The abstract states track all 18 tape cells at coordinates [-10,7], head offset and six live control states. The boundary configuration is E scanning 0, with left stack `00(10)^3 11` (nearest first) and every one of the 128 right seven-bit prefixes. All right excursions can reenter at coordinate 7 in **any** of the six control states. Exploration stops at first contact with the untouched left terminal marker, physical blank-left F/0 return, or F/1 halt. Marker contact must be **C reading 1**.

The certificate contains **6,399 distinct encoded states** and its exact successor relation has **7,306 outgoing checks**, including all six remote reentry choices. Every one of the 128 initial abstract states belongs to the certificate. The generated Lean declarations are:

- `BB6.TreeCert.root_good`: the entire finite tree passes the table-specific safety and successor checks;
- `BB6.TreeCert.all_seeds`: all 128 abstract seeds are members;
- `BB6.TreeCert.safe_member`: all tree members satisfy legal bounds and C/1 marker safety;
- `BB6.TreeCert.successor_closed`: all explicit successors of every member also belong to the tree.
- `BB6.TreeCert.every_seam_path_safe`: every finite path, of arbitrary length, from each of the 128 certified E-boundary seeds remains safe under the abstract transition relation; this additional corollary compiled locally after the first CI run and is awaiting its own CI check.

**Local independent Lean compilation passed** on 2026-11-06 under 4.36.0-rc2. **Unmodified-repository manual [GitHub Actions run 42149481751](https://github.com/FlareZ123/bb6/actions/runs/42149481751) SUCCEEDED**, rebuilding the 200 proof leaves and master with the pinned Lean toolchain. Exactly 200 separate leaf-block proofs were compiled, then the master imported and combined every block. `#print axioms root_good` returned `[propext]`, `all_seeds` returned no axioms, and `successor_closed` returned `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `sorryAx`, or `native_decide` occurs in the proofs.

Each Lean check uses `by decide` on at most 32 leaf values. The proof graph is a balanced binary tree rather than one giant array reduction, avoiding the memory blow-up observed when attempting a monolithic `by decide` on 6,399 states.

**Finite-certificate scope and completed transport:** The generated tree still uses a literal copy of the 11 original D transitions, with kernel-certified safety, seed inclusion and full successor closure. The new `SourcePhysicalTransfer` plus `SourceSeedMatch` prove the exact missing connection to the unchanged original source and arbitrary finite right tapes; `SourceSeamComplete` imports this proof and the tree in CI 42556565817. Prepared E-sector classification is now original-source certified. The authentic D blank-root decision is separate and remains open.

## Reproduction

The [generator](make_e_seam_kernel.py) reads the original Agent 31 certificate. It emits `ESeamTreeBase.lean`, 200 `ESeamTreeBlock*.lean` files, and `ESeamTreeMaster.lean` into a caller-specified output directory, using locked atomic writes. It needs Python 3.10+ and `filelock`. Compile the base first, each independent block with the base in `LEAN_PATH`, and finally the master with all blocks accessible. The repository's manual-only workflow [agent25-e-seam-kernel.yml](../../.github/workflows/agent25-e-seam-kernel.yml) automates this and prints the kernel axiom audit.

The Python generator and the 6,399 state text file are **untrusted inputs** to the Lean verification. If either were changed to include a forbidden marker or omit a necessary successor, a required generated proof would fail. Tree membership itself is proved sound by a generic Lean structural induction (`certified_member`) independent of the state-file generator. The proof does not require external synthesis to trust an assertion about safety or closure.

## Independent mechanism discrimination: A versus E

Using a second direct original-table finite-window enumerator, Agent 25 recovered the exact E m=3 counts: 6,399 states, 7,306 successor checks, 95 marker states, all C/1. The analogous **A** m=3 stack `0(10)^3 11` with the same right radius 7 has **4,733 states**, **5,462 successor checks**, and first-marker entries in **C/1 (94 abstract states)** or **A/1 (16 states)**. A literal physical trace starting from that A boundary with right suffix `111` first visits its terminal marker at primitive step 22 in A/1; the m=7 counterpart first visits the marker at step 38 in A/1. Thus the E-only all-C/1 first-marker argument cannot be transplanted unchanged to the A branch. This is a computational mechanism warning; Agent 2 and Agent 37 already documented nonconstant A timing shifts, so no standalone originality is claimed.

## Second kernel-checked finite invariant: A-boundary seam

The new [A-boundary generator](make_a_seam_kernel.py) reuses the same balanced-tree reflection method on the other alternating-stack boundary of D. Here the raw source state is **A scanning 0**, left nearest-first word `0(10)^3 11`, all 128 possible seven-bit right prefixes, and signed tracked interval [-9,7]. The first encounter with the left marker occurs at coordinate -8.

An independent raw-table, nondeterministic right-excursion BFS generated **4,733 distinct abstract states** and **5,462 outgoing successor edges**. Source-local enumeration gives 110 marker states: 94 C/1 and 16 A/1. The same finite graph is now formally validated by Lean in **148 independent blocks** (32 leaves or fewer per block) followed by a composed all-members theorem.

The exact formal guard is:

```
safe v =
  (head/state/tape bounds)
  && (at_marker → ((state = C || state = A) && scanned_one))
```

Consequently `BB6.TreeCert.every_seam_path_safe` proves for **every finite abstract path from any one of the 128 original-table A-boundary seeds** that marker contact, when it happens, is in C/1 or A/1. As with the E certificate, source-level physical-tape simulation into this abstraction is a separate formal obligation; the proof covers the stated abstract system without a step cutoff.

Additional **finite computational evidence** for m=3..12 at right radius 7 gives exactly 4,733+252*(m-3) visited states and 5,462+252*(m-3) abstract edges, while the 94 C/1 and 16 A/1 marker-state counts remain fixed. This is a tested finite range, with no quantified all-m theorem.

The A classification has a genuinely different marker-contact mechanism from the E all-C/1 result. The A1 alternative is witnessed by the concrete finite suffix `111` and is consistent with earlier observations of variable timing curvature under A stack shifts. This is a new Lean validation of a finite abstract safety statement in the repository; external mathematical novelty and root relevance remain unestablished. [A-boundary CI workflow](../../.github/workflows/agent25-a-seam-kernel.yml) is manual-only. **[GitHub Actions run 42150279323](https://github.com/FlareZ123/bb6/actions/runs/42150279323) SUCCESS**, confirming the independent original-table A graph and all 148 generated kernel proof blocks against unmodified repository sources.

## Next mathematical work

**Apply the newly certified prepared-E theorem to a source-proved genuine D blank-return section.** Derive a complete first-return grammar for any E prefix `I_(3q+4)(0 ys)` by composing `CryptidBoundary.prefix_E` and the theorem above, with the original positive-time no-return prefix lemma. Then prove a root-sensitive invariant covering the A, B and exceptional E suffix branches of the actual blank orbit. No global D halting verdict or BB(6) upper bound follows yet.
