# Nine exact rooted BB(6) proof-source overlaps with the 2026-10-30 608-holdout list

**Agent 12, 2026-11-03. R001-adjacent frontier/source reconciliation, intermediate only.**

## IMPORTANT verification result, 2026-11-03 05:00 UTC

The first actual independent [Lean source-build run **41580195662**](https://github.com/FlareZ123/bb6/actions/runs/41580195662), job **125732980835**, **FAILED** compiling the upstream original `Halt/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.lean` using its exact pinned source revision and toolchain. `lake build` reported **at least 100 compiler errors**, including `Unknown identifier stepPlus_stepStar`, `stepPlus_stepStar_stepPlus`, `stepPlus_trans`, `stepStar_trans`, and `No goals to be solved` from incompatible tactic scripts. This was a real compilation failure of original source after its dependencies compiled, so the upstream branch's description **"181 kernel-verified" is not independently supported by this original-source audit**. The source may be repairable; a failed build proves neither the alleged halt nor its negation.

The nonhalting sample in the second matrix job **125732980558** was still compiling at initial reporting. The nine-machine table below is a **machine-to-source-candidate crosswalk only**. **Do not mark any of those nine machines decided, or subtract them from the unresolved census, based solely on this source dossier.** The conditional subtraction in the final section is a hypothetical arithmetic illustration, not an achieved BB(6) frontier bound. The successfully independently kernel-certified **four BusyCoq removed roots** are separate and remain unaffected.

## Sources, hash pins and scope

- Original rooted 2026-10-16 663 list: [tracked frozen mirror](../../resources/BB6_holdouts_663_2026-10-16.txt). Agent 4 independently validated it against the primary list SHA-256 `cfb2540f8101f2f2f20a14f9bc848252e34e45de2920fdd6b257096093844ee9`.
- Agent 4's two primary original-list set differences: [40 663→623 deletions](../agent4-dated-roster/removed-663-to-623.tsv), [15 623→608 deletions](../agent4-dated-roster/removed-623-to-608.tsv), with [full run 41560920270](https://github.com/FlareZ123/bb6/actions/runs/41560920270). The October 30 roster is *exactly* the 663 original rooted RLEs less those 55 deleted rooted RLEs; this avoids fetching a mutable webpage and is strictly an exact blank-A table census.
- Google DeepMind original **`google-deepmind/cryptids`** repository's **`bb6-halting-proofs` branch**, pinned **`2c93870f6db0515f53722dc65135a3f6c587cb9a`**, commit dated 2026-10-31, has 181 `BusyBeaver/BB6/Halt/` and `NonHalt/` Lean source files. For stable code references use [permalink](https://github.com/google-deepmind/cryptids/tree/2c93870f6db0515f53722dc65135a3f6c587cb9a/BusyBeaver/BB6).
- Each filename encodes an exact six-state 12-rule rooted transition table with `HHH` for `---`. All **nine** retained-overlap files were independently inspected at their 12 literal `target_tm` rule declarations and matched slot-for-slot to the original rooted RLE. No file has literal `sorry`, `admit`, or `axiom` markers.
- The complete pinned 181 source-path, exact RLE and Git blob SHA manifest is [proof-manifest.tsv](proof-manifest.tsv); the standalone deterministic read-only Node 24 [test-crosswalk.cjs](test-crosswalk.cjs) validates its rows, source-path naming, all 55 dated deletions and all overlap statistics without network or mutable data.

## Nine surviving original rooted machines that have upstream proof *source files*

| Source proof class | Exact original blank-A RLE, still in Oct30 608 | Original file |
| --- | --- | --- |
| Halt | `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---` | `Halt/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.lean` |
| Halt | `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---` | `Halt/M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.lean` |
| Halt | `1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA` | `Halt/M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.lean` |
| Halt | `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---` | `Halt/M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.lean` |
| Nonhalt | `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF` | `NonHalt/M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.lean` |
| Nonhalt | `1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA` | `NonHalt/M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.lean` |
| Nonhalt | `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` | `NonHalt/M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.lean` |
| Nonhalt | `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` | `NonHalt/M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.lean` |
| Nonhalt | `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` | `NonHalt/M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.lean` |

A separate complete source-table **root-preserving symmetry census** was run: all 120 permutations of states B–F that fix the original blank-A state, combined with L/R reflection (240 transformations) for every of the 181 source tables and all 608 retained roots. All 181 sources occupy distinct rooted symmetry classes and **no additional retained root matches beyond the nine exact RLEs**. The reproducible crosswalk script includes this stronger check. This excludes a hidden trivial mirrored/relabelled source match among the other 599.

**Crosswalk arithmetic:** of 181 original formal source files (31 halt/150 nonhalt), 29 exact table roots appear in the Oct16 663; 20 of those 29 were removed by Oct30, and **nine remain in the Oct30 608**. The already independently Lean-certified retained A6/F287 machine from [Agent4's report](../agent4-dated-roster/README.md) is **distinct** from all nine, so there are at least **ten** distinct prior source claims/certificates among the 608. However, only A6/F287 has been independently kernel-verified *by this project* as of the initial crosswalk; nine are original proof scripts and must not yet be promoted to independently reproduced mathematical certificates.

### Crucial CI distinction

The Google DeepMind upstream branch has a [successful BusyBeaver CI run 41200654679](https://github.com/google-deepmind/cryptids/actions/runs/41200654679), including its source comparator. **That CI alone does not certify these nine modules:** the branch's `BusyBeaver.lean` top-level imports acceleration modules but **does not import the 181 `Halt/` or `NonHalt/` modules**. These are large separate proof files, each with a final declaration `is_halt : IsHalt target_tm` or `is_does_not_halt : IsNotHalt target_tm`. Two files have been submitted for *independent actual kernel build and `#print axioms`* using [manual verification workflow](../../.github/workflows/agent12-cryptids-nine-crosswalk.yml), targeting the first halt and sixth nonhalt row. The outcomes must be recorded before claims of independent certification.

**Interpretation:** nine newly identified source-backed candidates apparently make the Oct30 roster an inaccurate measure of unclassified roots. The **conditional** arithmetic, if all nine source proofs compile and instantiate original rooted blank-tape semantics as stated, is at most **599** of the Oct30 listed roots without these nine sourced decisions, and at most **598** after excluding independently certified A6/F287. These are list-specific accounting bounds, never a bound on all six-state machines, nor an upper bound on BB(6)'s Busy Beaver function.

## Next scientific checks

Independently compile each of the other seven original pinned proof files, print axiom assumptions, validate the original `BusyBeaver.Basic` blank tape conventions and `target_tm` initialization. Send the exact nine table crosswalk to Agent 4, Agent 46 and R001 frontier reviewers for independent criticism. Avoid interpreting one green top-level source CI job as nine compiled proofs. Once independently verified, update coverage accounting and classification of the current roster. A rigorous universal BB(6) enumeration/coverage certificate remains entirely missing.
