# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** Mathematical derivations, failed approaches, source references, finite data and chronology are preserved. Dated “pending”, “current” and “next” statements below refer to their original time and may be superseded. Use the maintained [summary](README.md) for current synthesis.

---

# Agent 36: conditional Cryptid D-start F-section trace

**Status (2026-11-02): intermediate computational investigation. No six-state machine is decided, no BB(6) bound is improved, and none of the newly proposed all-parameter macro identities is yet Lean-kernel certified.** The simulation is a testable projection, dependent on composing original-source F-return rules and proving the three hypotheses below.

Machine RLE: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

## Origin and implementation

Start with the source-certified primitive-machine equality `run(36, blank) = I_9(empty)` from Agent 31's `CryptidBoundary.blank36`. An `I_n(s)` configuration is F scanning zero, blank left half-tape and `1^n s 0^infinity` to its right. The script [trace.py](trace.py) represents `s` as a finite bit string; missing bits are zeros, leading ones are absorbed into `n`, and trailing zeros are removed.

Rules `B`, `E-pairs`, and `E-triple` come from Agent 31's `full_B` and Agent 32's `full_E_pairs`, `full_E_triple_pairs`, with successful original-source CI documented in [Agent32 README](../agent32-cryptid-third/README.md). The `A-pairs` rule is obtained by combining Agent 31's source-proved `prefix_A` with Agent 25's `ten_iter`, `iter_triplet`, and `a_pairs_triples`; the final **cross-encoding F-level bridge is not yet certified**. This qualification also applies to new A branches.

## Three new candidate universally quantified raw-machine identities

The following use arbitrary natural `k,q,r` and arbitrary finite binary suffix `y`. An initial `0` is the F-section delimiter. All step counts are exact hypotheses (each independently tested against the 12-instruction raw machine over the finite ranges stated below). Each line is an **unproved universal identity pending a Lean proof**.

1. **A-extra10**, from one remaining one after triples:
   `I_(3k+3)(0 (10)^q 1^(3r+1) 00 y) -> I_(8k+13+2q+8r)(y)`
   in `12k²+49k+48+4q+12r²+(24k+55+6q)r` primitive steps.

2. **A-E-pairs**, from two remaining ones followed by two zeros:
   `I_(3k+3)(0 (10)^q 1^(3r+2) 00 y) -> I_(8k+7+2q+8r)(0 1^6 y)`
   in `12k²+49k+54+4q+12r²+(24k+55+6q)r` primitive steps.

3. **E-double**, for `q>=1`, from two terminal ones:
   `I_(3k+4)(0 (10)^q 1100 y) -> I_(8k+5)(0 1^(2q+2) 0 1^6 y)`
   in `12k²+49k+60+4q` primitive steps. **Do not extrapolate to q=0**; the observed behavior there is different.

The first two formulas follow plausibly from Agent25's `a_ten`, `a_e_gate`, and `e_long` branch operators, combined with the known triple-loop recurrence and Agent31's initial-prefix result. The third needs an original-source E-boundary proof. None is asserted as a formal theorem merely because small-parameter simulations agree.

[verify_raw.py](verify_raw.py) independently runs the original 12-entry Turing machine, checking tape contents, F-zero state, blank left tape, and exact elapsed primitive steps for **1,728 A cases and 216 E-double cases**, using `k=0..5`, `q=0..5` (E: `1..6`), `r=0..5`, and several suffixes. The raw assertions pass locally on 2026-11-02. This is finite verification only.

## Reproducible conditional projection

Running `trace.py` for 30,000 macro applications from the `blank36` seed produces:

| Metric | Value |
|---|---:|
| Successful projected F-return applications | 30,000 |
| Final unary count bit length | 42,455 |
| Final total raw-step count bit length | 84,907 |
| Final explicit suffix | empty |
| B | 10,065 |
| A-pairs | 9,706 |
| E-pairs | 6,594 |
| E-triple | 3,423 |
| A-E-pairs (new) | 160 |
| A-extra10 (new) | 47 |
| E-double (new) | 5 |

SHA-256 of the serialized cumulative states `(n,suffix,time)` after each application, following [trace.py](trace.py): `14d9e7f849f56f27d818bca5cfc0ff6efa52a243a3674efff5249851b4b53ddd`.

The first A-extra10 branch appears at macro application 295 (zero-based index 294); the first E-double branch at application 8,395 (zero-based index 8,394). Earlier than these, the trace depends on `A-pairs` cross-encoding and existing certified source macros. **30,000 successful substitutions on one exceptional trajectory are no evidence of all-time closure or nonhalting**. More importantly, without global proof and an end-to-end blank-orbit composition, the huge numerical times have no status as verified lower bounds.

## Highest-value next steps

1. Formalize and source-check the three displayed arbitrary-parameter identities. Use the *unmodified* Agent31 `Boundary` source, and ideally integrate the `AAlternating` mechanism into that source to avoid manually translating two different configuration encodings.
2. Prove a small, reusable first-return relational theorem transporting any already verified `I_n(s) -> I_m(t)` identity to the original raw-machine `run`, then compose a finite trajectory via Lean's arithmetic evaluator rather than trusting the Python rewriting implementation.
3. Investigate whether the productive regular syntax of the suffix can be turned into an inductive reachable-language invariant. Beware of dependence on all higher ternary digits of the enormous unary counter: a 30,000-step trace is still finite.
4. Independently reproduce the above trace hashes and raw checks. Reject unsupported deductions about infinite behavior.

**No workflow runs on every commit.** The repository's other cryptid macro files and the first-gate record are in [Agent25's BLANK-GATE](../agent25-cryptid-doublezero/BLANK-GATE.md) and [Agent32 README](../agent32-cryptid-third/README.md).

## 15:50 UTC correction: universal A branches are now formally certified

Two previously speculative formulas in this dossier, **A-extra10** and **A-E-pairs**, are *specializations of Agent 35's earlier already-certified original-machine rules*, `full_A_code` and `full_A_code_double`. Agent 36 has now supplied the explicit all-parameter reduction in [AExtraBranches.lean](./AExtraBranches.lean). It substitutes token words `false^q ++ true^r ++ [false]` and `false^q ++ true^r`, proves the codeword, output-length, and exact step-count identities, and derives the two original-machine equalities for every `k,q,r` and every suffix `ys`.

**Full source Lean 4.36.0-rc2 check passed** in manual [CI 41474006959](https://github.com/FlareZ123/bb6/actions/runs/41474006959), compiling unmodified, SHA-checked Agent31 Boundary, Agent25 token definitions, Agent32 E rules, and Agent35 complete A bridges. Both final `#print axioms` are `[propext, Quot.sound]`; no `sorryAx`. This closes their former universal-proof gap but **must not be claimed as a new mathematical method**: the generalized results already belonged to Agent 35. The E-double q>=1 candidate was independently proven earlier in Agent35's `EDouble.lean`, and its q=0 continuation is source-certified in Agent32's `EZeroPair.lean`.

### Additional new A-side six-one gate

[ASixBoundary.lean](./ASixBoundary.lean) composes Agent35's general arbitrary codeword consumption with Agent32's **previously certified** `eSix_run`. It proves for *all* `k,q,r : Nat` and suffixes `ys` the exact original-source machine return

```text
I_(3k+3)(0 (10)^q 1^(3r+2) 0 111111 0 ys)
  -> I_(8k+11+2q+8r)(0 10101110 ys)
```

after precisely
```text
12k² + 49k + 62 + 4q + 12r² + (24k + 55 + 6q)r
```
primitive transitions. The stronger `full_A_code_six` theorem allows **any** interleaved `10` and `111` prefix instead of merely ordered `(10)^q(111)^r`. The proof is kernel-checked against all original unmodified dependencies, with only `[propext, Quot.sound]`, in [successful manual CI 41475009756](https://github.com/FlareZ123/bb6/actions/runs/41475009756). Independently, 1,080 raw primitive-step cases with k,q,r in 0..5 and five right suffixes matched exact full tape and time outputs. The universal source theorem is the evidence; finite tests are a separate falsification check.

This gate covers a **previously unhandled conditional trace pattern** in the D0 common-table B, C, F rooted starts at synthetic macro stages 6391, 12691, 7612 respectively, although no end-to-end Lean certificate for those enormous blank trajectories has been produced. Its method is composition of prior source-certified macros; external novelty is not claimed. All material remains `im-results/`.

### Multi-root conditional trace, corrected grammar

[trace_four_starts.py](./trace_four_starts.py) replaces the earlier rigid `(10)^q 1^(3r)` parser with an exact greedy **interleaved packet-code** scanner (`10` costs 2 and adds 1 to m; `111` costs `6m+41` and adds 4). Its exits correspond to existing source-proved `A-code`, `A-code-double`, and the new `A-code-six` return; E zero-pair `1100` at q=0 uses the older source-certified Agent32 theorem. Every branch has its own original-machine *universal conditional* Lean proof, but this Python program is **not itself a source-verified composition**.

Input seeds and authentic original raw prefix offsets are exactly Agent3's source-checked D0 table blank A/B/C/F to `F0Pure`: (n,time)=(9,36), (5,15), (15,92), (39,403); the original D3, D2, D1 rooted starts transform to shared D0 blank B,C,F respectively under already proved renaming/reflection. **All four projected traces successfully execute 30,000 symbolic returns** with the expanded grammar, with final unary-counter bit lengths 42,455; 42,454; 42,456; and 42,457 for D0-A,D3-B,D2-C,D1-F respectively. This is a computational finding about the grammar, *not* source-certified survival up to the astronomical symbolic times. In particular, absence of a halt in 30,000 substitutions does not establish an infinite invariant or a BB(6) bound.

For the D0-A seed, the new token scanner independently reproduces the earlier `trace.py` 30,000-step cumulative-state digest **`14d9e7f849f56f27d818bca5cfc0ff6efa52a243a3674efff5249851b4b53ddd`**, including the actual blank 36-step offset. Novelty of the exact macro rules must be credited to Agents 25, 31, 32 and 35. The remaining research requirement is a quantified **forward-closed right-suffix grammar from each true blank origin** or an original-machine halting witness; finite traces are insufficient.
