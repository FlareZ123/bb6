# D Cryptid: experimental first-physical-event timing shift outside the regular grammar

**Agent 37, 2026-11-05. Intermediate computational research, not a proof, blank-root decision, or BB(6) bound.**

## Exact question

Original six-state, two-symbol transition table:
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.
Use `I_n(s)` for the physically blank-left F-on-zero configuration, with right tape `1^n s 0^∞`. The **first event** after time zero is either entry into the undefined F/1 transition or an F/0 configuration whose entire physical left tape is blank. Syntactic F/0 with nonblank cells left does not qualify. Require `n>=2`.

**Conjectural arbitrary-suffix first-event cocycle.** For every fixed finite binary suffix `s`, branch residue `r∈{2,3,4}`, and `k>=0`, let `n=3k+r`. Suppose the first event of `I_n(s)` is defined in finite time. Then the first event of `I_(n+3)(s)` should have the same type. If it is a return to `I_b(t)`, the shifted start returns to `I_(b+8)(t)`. If it is a halt, both starts halt. In addition, there should exist an integer `m=m(r,s)>=0`, **independent of k**, such that if `T_k` is the first-event time:

- Return: `T_(k+1)-T_k = 24k+61+24m`, equivalently `T_k=12k²+(49+24m)k+T_0`.
- Halt: `T_(k+1)-T_k = 24k+53+24m`, equivalently `T_k=12k²+(41+24m)k+T_0`.

For a halt, the test reports the count of *executed defined transitions* before encountering F/1; the original source model enters frozen state 6 on the next transition. The constant shift cancels when comparing times.

**These are conjectures.** Finite tests also cannot establish that every input eventually has an event. The first-event claim excludes interior nonblank-left F-state visits.

## Finite raw-table evidence

The standalone [shift_first_event.cpp](shift_first_event.cpp) directly implements the eleven defined machine entries, using an explicit two-way tape and a live count of 1 bits strictly left of the head. It canonicalizes the whole right infinite-blank suffix at each qualifying first return. No regular macro model or original-source theorem is imported by the simulator. It compares each start with its n+3 and n+6 shifts, testing equality of the physical outcome, the predicted +8/+16 unary changes, and the 24-step curvature of the timing increments.

On 2026-11-05 the checked-in C++17 program produced:

- **262,136** exhaustive encoded suffix comparisons: all bitstrings length 0–14 (32,767 encodings per unary seed), unary seeds 5,6,7,8,9,10,15,39. No mismatches or timeouts within 1,000,000 primitive transitions. 1,780 original starts halted as their first event.
- **5,000** pseudorandom suffix comparisons, `mt19937_64` seed `20261105`: suffix length 1–160 (first bit 0, last bit 1), `k=0..35`, `r∈{2,3,4}`. No mismatches or timeouts within the same cap; 39 first-event halts. Observed `m` frequencies: `m=0:4720, m=1:244, m=2:33, m=3:2, m=4:1`.
- An independently coded earlier 90,000-trial finite replay for suffixes up to 24 bits and k=1..20 likewise found no mismatch; the checked-in executable is the primary reproducible evidence.

Encoded suffixes with terminal 0 may physically coincide with shorter suffixes; 262,136 counts input encodings rather than distinct physical tapes. Both sets of tests are finite empirical evidence. They do not certify a universal law.

## Internal prior art and mathematical obstacle

Important prior work already proves comparable claims within restricted languages. Agent 2's [DRegularDurationShift.lean](../agent2-cryptid-continuity/DRegularDurationShift.lean) and [DRegularTimedShift.lean](../agent2-cryptid-continuity/DRegularTimedShift.lean) kernel-prove analogous quadratic time laws for its eleven-case **regular** source-connected grammar, including arbitrary numbers of designated returns. Agent 37's [ReturnShift.lean](../agent37-cryptid-model-bridge/ReturnShift.lean) source-certifies an arbitrary A-token family. Agent 2's [boundary-shift study](../agent2-cryptid-continuity/2026-11-03-b-first-and-boundary-shift.md) already reports qualitative finite comparison evidence and a source-certified failure of an **unguarded all-stack** shift: E boundary length 0 halts while length 4 returns. This report does not claim novelty for regular cases or qualitative shift evidence.

The missing assertion is a complete source-connected **all-arbitrary-suffix first-event** conjugacy encompassing exceptional E packets, halts, the exact physical return predicate and first-return minimality. Agent31's [universal prefixes](../agent31-cryptid-boundary/README.md) reduce `I_(3k+r)(0s)` to B/A/E boundary stacks `m=4k+3`, with exact quadratic costs. A possible proof route is a *guarded four-extra-pair simulation*: consuming each triple-token would add 24 primitive steps to the time difference; final physical returns would contribute another 8 relative steps, unlike halts. This simulation is **unproved**, and a carefully chosen irregular input might invalidate it.

Even a fully established first-event cocycle would be an intermediate structural tool. Every unary n has some **synthetic** halting extension, already source-proved by Agent2 in [ExactFirstHalt.lean](../agent2-cryptid-continuity/ExactFirstHalt.lean). The **genuine blank-reachable suffix language** remains the deciding obstacle. The authentic D-family unary seeds 5,9,15,39 remain unresolved.

## Next discriminating action

Try adversarially structured, long irregular E/A packets for an actual counterexample, especially the source-certified E p=2 marker-mutating branch. If the rule survives, develop an original-source guarded alternating-stack simulation with exact halt/return timing. A useful eventual consequence must constrain an **entire actual blank-root feeder**, not merely produce another synthetic cylinder. Keep this evidence in `im-results/` until that mathematical gap is closed.


## Source-kernel-certified mixed-token halting first-event theorem (2026-11-05)

**Original six-state source proof now fully verified** in [manual CI run 42088127688](https://github.com/FlareZ123/bb6/actions/runs/42088127688). The two Lean modules [CodeHalt.lean](CodeHalt.lean) and [CodeHaltFirst.lean](CodeHaltFirst.lean) compile from the repository’s existing SHA-pinned, original Cryptid source using the expanded [agent37 manual workflow](../../.github/workflows/agent37-cryptid-halt-model-bridge.yml). Every new theorem has only standard Lean axioms; main exact first-physical-event theorem audit: \`[propext, Classical.choice, Quot.sound]\`, no \`sorryAx\`.

This theorem is a **universal infinite family of deliberately prepared synthetic F/0 initial tapes**. Let \`w\` be any finite Boolean token list, \`Code(w)\` map each false to \`10\` and each true to \`111\`, and let \`Y\` be any finite binary suffix. Define the original-machine configuration

\`H(k,w,Y)=I_(3k+3)(0 Code(w) 1101101100 Y)\`.

The fixed ten-bit \`1101101100\` is Agent2's previously source-proven A-boundary halting word. For every \`k,w,Y\` the actual original machine first enters state F scanning **1**, the undefined transition, at exactly

\`P(k,w)=12k²+41k+100+wordCost(4k+3,w)\`

defined transitions and enters the absorbing state 6 on the next transition, at exactly

\`T(k,w)=12k²+41k+101+wordCost(4k+3,w)\`.

**No halt occurs earlier**: \`BB6.Agent37CodeHalt.full_code_exact_first_halt\`. **No positive physically blank-left F-on-zero return occurs earlier**, even when a zipper left list contains explicit blank zero cells: \`BB6.Agent37CodeHaltFirst.full_code_first_physical_event\`, using \`c.l.all (!·) = true\`, not the overly restrictive syntactic condition \`c.l=[]\`. The fixed A terminal has a transient F/0 visit at local step 27 with nonzero cells to the left, correctly excluded. The all-parameter \`terminal_no_physical\` statement checks every local time \`0≤t<69\` for **arbitrary** left and right tails; the full theorem composes source-verified no-F initial prefix and no-F code consumption.

The strict first-event duration satisfies the exact *original-source* quadratic shift:

\`T(k+h,w) = T(k,w) + h(24k+12h+41+24#111(w))\`.

\`BB6.Agent37CodeHalt.codeTime_shift\` uses Agent37's prior unbounded source-certified \`wordCost_shift4h\`, and \`#111(w)\` is the number of \`111\` tokens in \`w\`. Taking \`h=1\` gives \`T(k+1,w)-T(k,w)=24k+53+24#111(w)\`, exactly the empirically seen **halt** side of the proposed arbitrary-suffix first-event cocycle. This checks a general difficult *halting* sector of that conjecture **rigorously**; the return-side and arbitrary other halting suffixes remain open.

**Novelty/provenance:** This extends earlier Agent2's \`AHaltCylinder.lean\` single fixed terminal cylinder and Agent35/25's unbounded A mixed-token consumer, by composing an arbitrary mixed code with the terminal, proving exact first halt, proving *strict physical first-event minimality*, and proving an all-h one-parameter timing cocycle. It shares key ingredients with existing source theorems, and independent external novelty is **not established**. Such input cylinders can deliberately be constructed to halt for any k; no theorem here says the original blank orbit produces one. It belongs in \`im-results/\`, not \`results/\`; no new BB(6) bound or resolved holdout follows.

Further useful goal: prove the all-suffix four-extra-pair first-event simulation, with exact time curvature, **including E exceptional and halting branches**; then apply any resulting source theorem to a genuine root-ancestry restriction. The arbitrary-suffix first-event conjecture itself remains purely computational outside the certified prepared families.


## Additional adversarial packet stress and genuine blank-root follow-up (19:10 UTC)

The [structured-packet stress test](check_structural.cpp) uses five fixed families of length-variable E and mixed A-code packet suffixes, some with 240 token repetitions and deeply irregular marked continuations. For `11,000` deterministic pseudorandom parameter selections (seed `202611051907`, k=0..129, r∈{2,3,4}), the same independent original-table first-event clock comparison passed **11,000/11,000**, including **719 halting first events**, with a five-million primitive transition cap, zero timeouts and zero timing/output contradictions. The previous one-million-step cap timed out on 26 deeply coded cases; increasing the cap resolved all 26. This is stronger *experimental* evidence for the all-suffix conjecture, but it remains an unproved statement.

A distinct, **genuine blank-orbit** follow-up uses Agent25's original-source eleventh return and new universal q=7 E/A rule, a potentially higher-value next result. The [TwelfthPacket.lean](TwelfthPacket.lean) **submitted proof** says for all t:

`I_(9t+10)((01)^7 1)`
`--[108t²+291t+230]--> I_(24t+21)(0 1^14 0 1^6)`
`--[768t²+2312t+1776]--> I_(64t+91)((01)^3 1²)`

Original primitive transition counts are validated by [check_q7.cpp](check_q7.cpp) on 35 entire two-return raw traces for t=0..34 (zero discrepancies). The proposed source-level `two_returns` theorem imports unchanged `EAllDouble.lean` and `A110111CodeFirst.lean` with `BoundaryPadding.ObsEq` to handle implicit right blanks.

[BlankTwelfthRejoin.lean](BlankTwelfthRejoin.lean) proposes an authenticated **actual blank-origin** lift: after the named eleventh root `I_(32768*(t11/27)+5493)`, `DRegular.run 1759` reaches the twelfth exceptional `L(9*t12+10,7,1)` (independent arithmetic predicts `a.bit_length=67194`, q=7,b=1, section index 47,483), and the above two returns land in `L(64*t12+91,3,2)`. The necessary prior Agent25 eleventh proof had an outstanding trivial unnormalized `oppairs 0=[]` goal in CI [42080082556](https://github.com/FlareZ123/bb6/actions/runs/42080082556); Agent37 patched it and exposed explicit root parameter. **Until the two source audits [42089068704](https://github.com/FlareZ123/bb6/actions/runs/42089068704) (eleventh) and [42089877845](https://github.com/FlareZ123/bb6/actions/runs/42089877845) (twelfth) succeed, the genuine blank-root extension is an unverified Lean submission.** The computational prediction is not equivalent to a source-certified root result. The twelfth return is still a very long finite prefix, far below the machine's potential ultimate behavior; it does not resolve any holdout.

The twelfth packet's proposed quadratic leading coefficient is **876**. It matches Agent2's independent packet-shift universal degree-two coefficient for two guarded returns: `Q₂ = 12(64²−9²)/55 = 876`. The full polynomial `876t²+2603t+2006` follows from direct algebra on the already defined E and A primitive-step costs (verified separately by symbolic integer simplification and by 35 exact raw-tape traces). This is a consistency check of two mathematical frameworks, not an independent proof of blank-origin applicability.

## Original-source twelfth genuine blank-origin theorem: VERIFIED 2026-11-05 19:18 UTC

**Update replacing the earlier verification-pending qualification for the twelfth extension:** [manual GitHub Actions run 42089877845](https://github.com/FlareZ123/bb6/actions/runs/42089877845) **SUCCEEDED**. The original source was restored from the repository's pinned bundles and the full DRegular/source proof dependencies were compiled with Lean 4.36.0-rc2. Final kernel audits:

- `BB6.Agent25EleventhRoot.blank_eleventh_reentry_exact`: `[propext, Classical.choice, Quot.sound]`.
- `BB6.Agent37TwelfthPacket.two_returns`: `[propext, Quot.sound]`.
- `BB6.Agent37TwelfthRoot.terminal1759_exact`: **no axioms**.
- `BB6.Agent37TwelfthRoot.blank_twelfth_exception`: `[propext, Classical.choice, Quot.sound]`.
- `BB6.Agent37TwelfthRoot.blank_twelfth_reentry`: `[propext, Classical.choice, Quot.sound]`.

**Actual blank-origin theorem:** for `t12 = ((DRegular.run 1759 seed12).getD default).a-10` divided by 9 as defined in [BlankTwelfthRejoin.lean](BlankTwelfthRejoin.lean), and exact symbolic `reentry12Time` defined in that file, the all-blank original D0 machine has a physical F/0 section `L(64*t12+91,3,2)`. This is the twelfth exceptional episode, regular-model section index 47,485 (first exceptional section index 47,483); the incoming exceptional source `L(9*t12+10,7,1)` is reached after precisely 1,759 regular returns from the eleventh certified blank-root reentry. The universal transition [TwelfthPacket.lean](TwelfthPacket.lean) gives `876*t12²+2603*t12+2006` original primitive transitions for the exceptional E then A macro. Every source step is proved in the original six-state machine, with physical `ObsEq` handling implicit terminal blanks.

This is a **new finite genuine blank-ancestry checkpoint within this repository**; it neither determines the D-machine's eventual behavior nor any value of BB(6). External mathematical novelty is not claimed; keep under `im-results/`, not `results/`. Next proposed arithmetic extension: 3,679 regular sections lead to a thirteenth E exception `L(a,6,1)`, `a%9=4`; authenticate via the previously proved general E/B exceptional source theorem and record an explicit source transport into the true blank root. Independent arithmetic regression is [check_root12.py](check_root12.py).
