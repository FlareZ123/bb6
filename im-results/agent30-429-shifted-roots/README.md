# BB429: 686 certified blank-root terminal residues excluded at modulus 262144

**Research status, 7 November 2026:** Unchanged-source Lean 4.36.0-rc2 [CI 42348808379](https://github.com/FlareZ123/bb6/actions/runs/42348808379) **PASSED**, checking thirteen new infinite root-specific forbidden rays and the exact merged `686`-class gate. The first four of those rays independently passed pinned, unchanged **original Google DeepMind Cryptids raw six-state machine** [CI 42347463517](https://github.com/FlareZ123/bb6/actions/runs/42347463517). The separate pinned raw-source full `686` integration [CI 42348810430](https://github.com/FlareZ123/bb6/actions/runs/42348810430) **is still running**; its conclusion must be verified before calling that particular larger raw-machine theorem checked.

**The full BB(6) problem, and machine #429's genuine blank-start halting status, remain open.** This is a source-kernel-verified *necessary condition*, stored under `im-results/` because external novelty and publishability have not been established. No claimed terminal residue is known reachable.

## Exact mathematical result

Let `BB429.run n (0,0)=some (a,b)` be the authentic initial trajectory of the local accelerator for the six-state, two-symbol machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. Its exact halting gateway is `b+1=2*a`.

The source-checked [BB429Combined686.lean](BB429Combined686.lean) theorem `blank_halt_not_686` proves, **for all natural numbers** `n,a,b`, that an actual blank-root state on this terminal line satisfies
```
a % 262144 ∉ excluded686
```
where `excluded686` is the explicit union of Agent 1's 673 original forbidden classes and **thirteen newly certified, previously surviving residues**. The file proves `excluded686.length=686` and `excluded686.Nodup` in Lean's kernel.

Combined with the preexisting 58-class true-root terminal predicate modulo 16384, whose 16-fold expansion consists of 928 candidates modulo 262144, `BB429Combined686.still242` is an **exact necessary candidate list of length 242**, all distinct. Its proved `still242_iff` theorem states
```
a % 262144 ∈ still242 ↔
  a % 16384 ∈ BB429SurvivorMask.base58 ∧
  a % 262144 ∉ excluded686
```
These 242 classes are *arithmetic survivors* only. The theorem establishes no reachability among them. The original root remains unclassified and no upper bound for BB(6) follows.

The thirteen new entire infinite forbidden families, with `r` always denoting the first-counter residue, are:

| Uniform modulus A | Forbidden residues r | Source lemma |
| --- | --- | --- |
| 32768 | 765, 3281 | [BB429ShiftRays.lean](BB429ShiftRays.lean) |
| 262144 | 2385 | [BB429ShiftRays.lean](BB429ShiftRays.lean) |
| 131072 | 16381 | [BB429ShiftRays.lean](BB429ShiftRays.lean) |
| 262144 | 6141, 19665, 49149, 65533, 81917, 98301, 114685, 163837, 229373 | [BB429MoreShifted.lean](BB429MoreShifted.lean) |

For each listed pair `(A,r)` the Lean proof excludes **every** source-root affine terminal state `(A*q+r,2*A*q+2*r-1)` for **every** `q≥0` and source time. There is no finite parameter cap and no large-number simulation heuristic in this statement. The four coarse-modulus rays eliminate precisely four more representatives from the former 255 survivor list; the nine additional representatives eliminate nine more, giving `255−13=242`.

## How the proof works

All thirteen rays use Agent 30's previously source-checked [`BB429Kernel16.cert_sound`](../agent30-429-even16/BB429InverseKernel16.lean), a mathematically sound symbolic inverse certificate over the **whole natural parameter domain**. For each residue `r`, the source checker evaluates the finite depth-16 inverse certificate at shifted affine offset `(A,A+r,2*A,2*A+2*r−1)`. This proves every positive quotient `q+1` by substituting the parameter `q`. The previously missing zero quotient is discharged from the *genuine blank root* using strict monotonicity of the exact rank `2a+b` along successful runs.

The four original new rays use individual true-root consecutive rank straddles:

| Missing zero-quotient target | Certified crossing macro time | Genuine run before | Genuine run after |
| --- | ---: | --- | --- |
| (765,1529) | 638 | (9,3040) | (21,3019) |
| (3281,6561) | 3171 | (25,13073) | (53,13020) |
| (2385,4769) | 2246 | (3069,3396) | (0,9544) |
| (16381,32761) | 16107 | (16396,32722) | (0,65524) |

The nine later rays share a stronger **reusable root-rank lemma** `BB429MoreShifted.no_terminal_below_rank`. Lean checks the exact successful original-root endpoint
```
BB429.run 240000 (0,0) = some (196605,529002)
```
whose rank equals 922212. It follows, by a split on source time before/after this checkpoint, that **no terminal configuration of strictly smaller rank can ever be reached**: an earlier terminal would prevent this successful checkpoint, and a later terminal would violate the all-time rank monotonicity. All nine zero-quotient terminal targets have rank less than 922212. The 240,000-step proof is reconstructed in source Lean from 240 exact 1,000-transition checkpoints; each finite block is checked by `decide`. The single endpoint replaces nine separate root straddles, while inverse soundness handles the unbounded tails.

This general rank-barrier lemma can be reused for future shifted cylinders, though continued finite modular refinement alone is not a complete machine decision.

## Original raw Turing-machine provenance and audit boundaries

- **Verified original accelerator plus combined 686 gate:** [CI 42348808379](https://github.com/FlareZ123/bb6/actions/runs/42348808379), workflow [agent30-429-shifted-roots.yml](../../.github/workflows/agent30-429-shifted-roots.yml), compiles unchanged `BB429Rank`, parity/root constraints, affine inverse soundness, Agent 1's 673-class sieve and exact predecessor survivor representation, the four first ray proofs, the 240k-checkpoint extension, and the `686/242` cardinality theorems. The earlier stages passed [42347188987](https://github.com/FlareZ123/bb6/actions/runs/42347188987), [42348114459](https://github.com/FlareZ123/bb6/actions/runs/42348114459), and [42348461286](https://github.com/FlareZ123/bb6/actions/runs/42348461286).
- **Verified original raw six-state bridge for first four rays:** [SourceRawHaltShift.lean](SourceRawHaltShift.lean) passed [pinned CI 42347463517](https://github.com/FlareZ123/bb6/actions/runs/42347463517) against the unchanged original [Google DeepMind Cryptids](https://github.com/google-deepmind/cryptids) Turing-machine module at SHA `c86f15861709b76042998c5211c7b2f83991621b` under Lean 4.35.0-rc4. Its exact raw-machine halting iff retains the actual source terminal witness and adds the four new exclusions.
- **Expanded original raw six-state bridge awaiting independent CI conclusion:** [SourceRawHalt686.lean](SourceRawHalt686.lean) uses the same previously verified `source_run_to_local` and `source_next_none_to_local` bridge and original 38-class raw halt theorem. It formalizes `raw_halts_iff_686`: `IsHalt target` iff a **genuine source-root** terminal event satisfies the earlier 38/1024 constraints and avoids all 686 new forbidden residues. [Pinned raw-machine audit 42348810430](https://github.com/FlareZ123/bb6/actions/runs/42348810430) is currently pending; do not treat an unverified edit as an additional original-machine audit.
- All source theorem files use ordinary Lean 4 proof tactics and kernel computation, with no `sorry`, `native_decide`, or replacement successor map in the published proofs. The workflows inspect `#print axioms` and reject unexpected `sorryAx`. Exploratory Python/JavaScript inverse checks and temporary mock-interface compilation were used only to choose candidates; they are **not** the evidence for the checked theorem.

## Next decisive research question

The source-verified [physical B/001 (equivalently C/01) fatal-event characterization](../agent32-429-raw-parent/README.md), the [one-sided last-writer theorem](../agent18-429-lastwriter/README.md), and the synthetic-vs-blank counterexamples remain the deeper #429 problem: either exhibit a **genuine blank-root** fatal event or exclude it for all time using a full-tape history-sensitive invariant. Source-defined inverse cylinders and arithmetic count reductions do not settle that existential. This exact 242-class executable mask is a useful residual filter for experiments on the genuine root, but synthetic starts satisfying excluded congruences cannot be promoted into real blank witnesses.
