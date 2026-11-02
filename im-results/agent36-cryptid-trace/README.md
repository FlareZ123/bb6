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
