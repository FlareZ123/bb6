# A universal arbitrary-right-tail E-boundary first-event cocycle

**Agent 31, 2026-11-06. Status: computer-assisted mathematical argument with two independent finite-state enumerators; the finite closure has NOT yet been kernel-verified in Lean.** This concerns the six-state D cryptid's *synthetic E boundary*. It is a substantial strengthening over finite suffix samples, but it does not decide the authentic blank-root trajectory, any BB(6) holdout, or BB(6) itself. Confirm novelty against external @-d analysis before publishing.

## Precise theorem derived from the finite certificate

For the literal two-symbol machine

`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`,

let `E_m(Y)` be its raw configuration in state E scanning 0, with all cells strictly to the left of the finite nearest-first word `00(10)^m11` zero, and with **arbitrary** right-hand binary tape `Y` (even one with infinite support). Require `m>=3`. The first *positive* physical event is either reaching state F scanning 1 (the undefined halt instruction), or reaching state F scanning 0 with the **entire left tape** blank. It is also possible that no such event ever occurs.

The finite certificate and the elementary marker-pumping proof below establish the following three-way classification relative to the same `Y` and `E_3(Y)`:

1. **Halt:** if `E_3(Y)` first reaches F/1 at time `H(Y)`, every `E_m(Y)` first reaches F/1 after *the same* `H(Y)` successful primitive transitions. Original-source frozen state 6 begins one transition later in each run.
2. **Return:** if `E_3(Y)` first physically returns to F/0 at `R(Y)` steps, `E_m(Y)` first physically returns after **`R(Y)+2(m-3)`** steps. Its F/0 endpoint has exactly `2(m-3)` extra consecutive 1s prepended to the full physical right tape at the `E_3` return, with the remainder identical. This is a full tape comparison, not only equality of unary lengths modulo three.
3. **No event:** if `E_3(Y)` never has a first event, neither does any `E_m(Y)`, `m>=3`.

Thus an adjacent four-pair shift `m ↦ m+4` preserves first-event type, adds **8 raw steps and 8 output ones** in the return case, and adds **zero steps** in the halt case, for *all right tapes and all m>=3*. This is stronger in logical scope than the bounded-suffix tests in Agent2/37's dossiers, assuming the finite-state abstract certificate is sound.

### Original F-section consequence

Existing original-source Lean lemmas `CryptidBoundary.prefix_E` and `BB6.CryptidPrefixFirstReturn.prefixE_positive_noF` map `I_(3k+4)(0Y)` to `E_(4k+3)(Y)` after `P(k)=12k²+41k+33` primitive steps without any intervening positive-time F state. Here `I_n` is the physical F/0 section with n leading right ones. Accordingly, the *first* F event from the original F/0 input obeys, for every `k>=0` and any fixed finite `Y`:

- On a **return** branch, first physical F/0 return time `12k²+49k+33+R(Y)`; output unary count and complete physical right tape equal the `k=0` return with `8k` additional initial ones.
- On a **halt** branch, first F/1 event time `12k²+41k+33+H(Y)`; frozen halt enters one primitive step later.
- If `k=0` has no first event, no `k` has one.

This proves the E-sector formulas conjectured in `im-results/agent37-d-timing-cocycle/README.md`, conditional on an independently audited finite closure. The B and A sectors are separate and **not** settled by this argument. In particular, no root-connected nonhalting or halting conclusion follows.

## Finite abstraction proving the base marker invariant

The only computational lemma needed for the all-m theorem is:

> **Base marker safety:** For every possible right tape `Y`, a run of `E_3(Y)` whose head first visits signed position **-9**, the first of the terminal left `11` pair, must be in state **C** scanning **1**.

The two initial terminal 1 bits occur at positions -9 and -10; they cannot be altered before that first visit.

The verifier `abstract_e_seam.py` represents an exact configuration *restricted to the finite window [-10,7]* by `(head,state,bitmask)`, while the head remains in that window and has not yet reached -9. The bitmask retains all 18 cells (including the scanned zero and the arbitrary 7-bit right prefix). Start from all **128 possible** assignments to right cells 1..7.

To account soundly for *every possible physical behavior to the right* of position 7, whenever a transition exits to position 8, the abstract machine nondeterministically jumps back to position 7 in **any one of the six live control states**, keeping every tracked cell as written at the exit. A genuine excursion through cells 8,9,... cannot modify a tracked cell until the head reenters at 7. Its actual state upon reentry is necessarily among the six choices. If it never returns, no marker visit occurs during the excursion. Early halts or physical F/0 events may stop a genuine run; allowing additional hypothetical reentries would only enlarge the abstract state set, making the safety check conservative.

The worklist explores *every* abstract successor of *every* reached abstract state until closure. It stops at an F/1 event, a physical F/0 event, or first marker contact. A forbidden marker entry triggers an exception. No right-tail distribution or finite primitive-time cutoff is imposed.

For `m=3,R=7`, the deterministic Python verifier reports exactly **6,399 reachable abstract states**, **7,306 successor checks** (including all nondeterministic reentries), and **95 marker states**, every marker state in **C/1**. The **independent C++17 bit-packed BFS**, `check_e_seam.cpp`, reports the identical numbers. As an additional check, both algorithms report at `m=7,R=7`: **7,159 reachable**, **8,066 transitions**, **95 marker states**, all C/1. Python runs for m=3..15 likewise passed, with `6399+190(m-3)` reached states; this finite observation is not used as an all-m proof.

The narrow abstract window radius 6 permits a spurious bad-marker path. Radius 7 closes safely. This is an important crosscheck against accidentally replacing remote behavior with unjustifiably restrictive assumptions.

### Why the finite check implies a universal safety fact

Induction on the actual primitive execution establishes a simulation into the abstract transition graph. Initially the tracked local window agrees for some one of the 128 right-prefix assignments. An actual local step is represented exactly. A rightward excursion crosses position 8 and must reenter the window from the right at position 7 if it ever reaches a position <=7 again; the arbitrary-state edge explicitly covers that possibility and leaves locally tracked cells unchanged. Every actual first marker entrance is therefore represented among the 95 abstract first-marker states. All 95 are C/1.

This abstraction is an **overapproximation**: spurious traces are permitted. Exhaustive safety of the *larger* graph therefore proves safety for every concrete right tape. The proof relies on source-table fidelity and correct exhaustive graph enumeration. The graph closure is reproducible from the two small source files without an externally supplied data file; a Lean kernel checker remains an important next validation task.

## All-m pumping proof from the base certificate

Assume `E_m(Y)` has the marker-safety property, with `m>=3`. Its initial tape and `E_(m+1)(Y)` are identical at every position to the right of the first terminal marker of `E_m`; the additional `10` pair is inserted at that marker, pushing the original terminal pair two positions left. As long as the shorter run has not reached its marker, the two deterministic raw Turing machine executions have exactly the same head, control state, scanned bit, time and all tape cells to the right of the marker. They cannot physically return to F/0 there because the untouched terminal `11` lies strictly to the left of the head.

If the shorter run halts first, the longer run halts at the same time. If the shorter run first reaches its marker, marker safety forces state C on a 1, and both runs reach that position simultaneously. In the shorter run, the two untouched terminal 1s execute `C/1 → D/1 → F/0` in **two transitions**. In the longer run, the newly inserted `10` pair executes `C/1 → D/0 → C/1` in **two transitions** and writes two 1s, after which the original untouched `11` pair produces the same final two-step F/0 return. The physical tape output differs by exactly two new leading 1s, and the return time by exactly two. No intermediate F/0 is physically blank-left because the untouched marker still lies left of the head.

This establishes marker safety for `m+1`, with its new terminal-pair entry in C/1, and the corresponding outcome/time/tape relationship. Ordinary natural-number induction, starting with the finite m=3 certificate, proves the claimed trichotomy and exact `2(m-3)` relationship **for all m>=3**. For runs that never reach their marker and never halt, the finite-prefix equality of both runs continues indefinitely.

## Scope, confidence, and next actions

The *mathematical induction* is independent of the abstract state's size and requires no estimate of halting time or right-tail length. The only computational trust base is the small **finite closure** at m=3 under the exact original 11 defined transition rules, plus the sound overapproximation. Both implementations were executed locally and agreed; the key result is reproducible without GitHub Actions.

The mathematically strongest outstanding action is to formalize the closure certificate in Lean 4.36.0-rc2, then use the unchanged original `Boundary.lean` source and Agent2's prefix no-F theorem for a kernel-verified final source-to-first-event implication. Until then, call this a **two-implementation computer-assisted proof**, not a Lean-kernel-certified theorem. Its novelty relative to external @-d/DeepMind work has not been established.

This theorem supplies a complete *first-event E-sector shift* for synthetic F/0 inputs, but gives no criterion deciding whether the base input `E_3(Y)` eventually returns, halts, or diverges for every particular `Y`. Nor does it decide whether the authentic all-blank orbit ever reaches a prepared halting suffix. These are essential distinctions for the BB(6) objective.


## Verification update, 2026-11-06 01:27 UTC: independently checkable finite invariant and original-source CI

The certificate is now published explicitly as [`ESeamClosedStates.txt`](./ESeamClosedStates.txt): exactly 6,399 distinct encoded triples. The additional [`verify_e_seam_certificate.py`](./verify_e_seam_certificate.py) is a **separate finite invariant checker**, requiring no worklist reachability search. It verifies all 128 possible initial windows are members, every state is safe at the marker, and **all 7,306** transition/reentry successors belong to the supplied set. Thus the 6,399-state set is a bona fide **finite inductive invariant** for the nondeterministic right-excursion abstraction, and closure can be audited independently of the algorithm that found it. The literal 11-entry D table appears separately in the verifier; the C++ implementation also independently reproduces graph cardinalities. For a paper proof, the simple mathematical implications are set inclusion, closure under transitions, and safety of all members.

The locally Lean-checked marker pump `ESeamPump.lean` has a further unchanged-original-source rendition [`ESeamSource.lean`](./ESeamSource.lean). **Original-source manual [GitHub Actions run 42143669887](https://github.com/FlareZ123/bb6/actions/runs/42143669887) succeeded**: it rebuilt the pinned `Boundary.lean` of the original D table, compiled `ESeamSource.lean`, ran the abstract Python enumeration, independent C++ BFS and the finite cylinder regression. The source marker-sweep theorem's only Lean axioms are the standard `propext` and `Quot.sound`. A follow-up CI run has been requested to also check the explicit certificate file, not only regenerate its graph. The finite safety closure is still not a Lean-kernel theorem; that remaining distinction is deliberate.

This upgrades the evidence from *two mutually agreeing enumerators* to a **fully explicit, externally independently verifiable finite inductive-invariant certificate** plus original-source Lean verification of the parametric marker pumping. The all-m E cocycle remains a mathematical consequence of this finite certificate and the stated simulation/pumping argument. It is still unrelated to the genuine D blank-root decision and does not give a BB(6) bound.
