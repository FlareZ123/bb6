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

## Source-kernel-certified mixed-token first-return theorem (2026-11-23)

The [cryptid-model-bridge result](../agent37-cryptid-model-bridge/FullWordPairsFirst.lean) now proves a strict first-event return for a second infinite prepared-input family, complementary to the halting cylinder above. For every `k,q≥0`, finite A-token word `ws` (arbitrary interleavings of `10` and `111`), and finite binary tail `ys`, the original-source configuration
```text
pairInput(k,q,ws,ys)
  = I_(3k+1)(0 · Code(ws) · 110 · (10)^q · 0 · ys)
```
reaches its first state-F configuration with every cell strictly left of the head blank at exactly
```text
T(k,q,ws) = pairTime(k,q,ws)
          = 12k² + 41k + 32
            + wordCost(4k+3,ws)
            + 2(4k+3+wordInc(ws)) + 16 + 4q.
```
The endpoint scans 0 (F/0), with left tape empty and right tape
`1^(2(4k+3+wordInc(ws))+1) · 0 · 1^(2q+6) · ys`. The proof excludes earlier blank-left F states across the unary prefix, the arbitrary mixed-token consumer, and the complete `110(10)^q0` terminal macro. The terminal macro's new `two_one_pairs_first_physical` theorem explicitly handles the qB/qD scans, the seven-step core, and the final D sweep.

The existing exact shift law is therefore a **first-event** law on this family:
```text
T(k+h,q,ws) = T(k,q,ws)
              + h(24k + 12h + 49 + 24·tripleTokens(ws)).
```
Original-source manual [CI 45182834918](https://github.com/FlareZ123/bb6/actions/runs/45182834918) succeeded; the exported theorem has axiom profile `[propext, Quot.sound]`, with no `sorryAx` or `native_decide`.

This is a restricted token-coded terminal family, not the conjectured arbitrary-binary-suffix cocycle for residues `r∈{2,3,4}`. It does not prove that the authentic blank-root orbit reaches these prepared inputs, and it does not decide BB(6). External novelty/publication eligibility remains unassessed.

## Next discriminating action

The token-coded `110(10)^q0` terminal family is now closed at first-event level by [FullWordPairsFirst.lean](../agent37-cryptid-model-bridge/FullWordPairsFirst.lean); do not spend more compute re-proving that branch. The next discriminating action is to try adversarially structured, long irregular E/A packets for an actual counterexample, especially the source-certified E p=2 marker-mutating branch. If the rule survives, develop an original-source guarded alternating-stack simulation with exact halt/return timing. A useful eventual consequence must constrain an **entire actual blank-root feeder**, not merely produce another synthetic cylinder. Keep this evidence in `im-results/` until that mathematical gap is closed.


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

This is a **new finite genuine blank-ancestry checkpoint within this repository**; it neither determines the D-machine's eventual behavior nor any value of BB(6). External mathematical novelty is not claimed; keep under `im-results/`, not `results/`. **Thirteenth extension: ORIGINAL-SOURCE CI VERIFIED 2026-11-06.** From the twelfth reentry `L(64*t12+91,3,2)`, exactly 3,679 regular sections reach `L(9*t13+4,6,1)`; the universal Agent25 E/B family with `p=4` returns to `L(64*t13+29,1,5)`. The proof is [BlankThirteenthRejoin.lean](BlankThirteenthRejoin.lean). Workflow run [42306192563](https://github.com/FlareZ123/bb6/actions/runs/42306192563) completed successfully on 2026-11-06, including the restored original-source dependencies and all eleven D-regular return cases.

The arithmetic replay now predicts four further exceptional sections from this thirteenth reentry:

| Episode | DRegular sections | Exceptional source | `t mod 27` | Unary parameter bits |
|---:|---:|---|---:|---:|
| 14 | 5,169 | `L(9*t14+4,5,1)` | 3 | 79,720 |
| 15 | 6,821 | `L(9*t15+4,8,1)` | 14 | 89,375 |
| 16 | 2,077 | `L(9*t16+4,5,1)` | 26 | 92,317 |
| 17 | 2,656 | `L(9*t17+7,7,1)` | 6 | 96,078 |

The arithmetic and little-endian SHA-256 fingerprints are reproducible with [check_root17.py](check_root17.py). Episodes 14–16 use the universal Agent25 E/B theorem with parameters 3, 6, and 3; their root reentries were compiled in the audit [43394857303](https://github.com/FlareZ123/bb6/actions/runs/43394857303), with episode 16 independently recompiled in [43534820371](https://github.com/FlareZ123/bb6/actions/runs/43534820371). Episode 17 has `t17=3u` and uses [ExceptionalE7ThirdReturn.lean](ExceptionalE7ThirdReturn.lean), a source theorem generalized to all `q=3r+1` and `t=3u`: EAllDouble, then full_E_three, then full_A_code_110111_first_return with code `(10,10,111^(2r-1))` and tail `(111)`. At the root's `r=2`, the endpoint is `L(8(64u+10)+39,3,2)`; the root transport [BlankSeventeenthRejoin.lean](BlankSeventeenthRejoin.lean) is source-verified in [43760695437](https://github.com/FlareZ123/bb6/actions/runs/43760695437).

The intermediate proofs are [BlankFourteenthRejoin.lean](BlankFourteenthRejoin.lean), [BlankFifteenthRejoin.lean](BlankFifteenthRejoin.lean), and [BlankSixteenthRejoin.lean](BlankSixteenthRejoin.lean). The 14–16 root transports were compiled in [43394857303](https://github.com/FlareZ123/bb6/actions/runs/43394857303), with episode 16 independently reproduced in [43534820371](https://github.com/FlareZ123/bb6/actions/runs/43534820371); episode 17 was source-verified in [43760695437](https://github.com/FlareZ123/bb6/actions/runs/43760695437).

**Verified eighteenth reentry:** The DRegular replay gives episode 18 at index 70,800 after 2,902 regular sections, reaching `L(9t18+4,3,1)` with `t18 mod 27 = 22` and a 100,189-bit unary parameter. The E/B general source return at `p=1` closes the exception at `L(64t18+23,1,5)`. The split source audit succeeded in [stage 1, arithmetic](https://github.com/FlareZ123/bb6/actions/runs/44078315654), [stage 2, authentic-root lift](https://github.com/FlareZ123/bb6/actions/runs/44288454765), and [stage 3, E/B reentry](https://github.com/FlareZ123/bb6/actions/runs/44289033894), using source `20509b53af45edce5b8a145e8714245d3d225cdd` and extension snapshot `2dcc75abcf2e0ca06c877336fad1d2d8d07e0abd`; the workflow's standard-axiom/forbidden-axiom gate passed.

**Arithmetic lookahead beyond the verified eighteenth reentry, not yet source-CI verified:** the corrected E/E/A endpoint is `L(512u+119,3,2)`. The DRegular replay, reproducible with [check_root17.py](check_root17.py), then predicts:
- Episode 19: index 80,582 after 9,780 regular sections, reaching `L(9t19+10,9,1)`, with `t19 mod 27 = 12` and 114,030 bits. The existing E/A general theorem at `p=2` returns to pure unary `L(64t19+113,0,0)`.
- Episode 20: index 82,624 after 2,040 regular sections, reaching `L(9t20+7,5,1)`, with `t20 mod 27 = 4` and 116,920 bits. This is the `k=3t+1`, `t=1 mod 3` third-return E/E/E escape family.

The [ExceptionalE7ThirdReturnEscape.lean](ExceptionalE7ThirdReturnEscape.lean) module formalizes the general `q≥3`, `t=3u+1` three-return E/E/E source route, reaching the off-L packet `I_(8*(64u+31)+9)(P4 0 1^(2q-6) 0 1^6)` through EAllDouble, full_E_three, and full_E_triple_pairs; this source theorem passed CI [43761344093](https://github.com/FlareZ123/bb6/actions/runs/43761344093). Root transports exist for [BlankEighteenthRejoin.lean](BlankEighteenthRejoin.lean), [BlankNineteenthRejoin.lean](BlankNineteenthRejoin.lean), and [BlankTwentiethEscape.lean](BlankTwentiethEscape.lean). Episode 18's E/B return is now source-verified in [44289033894](https://github.com/FlareZ123/bb6/actions/runs/44289033894); The monolithic stage-3b run [44289702591](https://github.com/FlareZ123/bb6/actions/runs/44289702591) ended with runner shutdown (exit 143) before any Lean diagnostic. The replacement split audit passed checkpoints 1 [44307926048](https://github.com/FlareZ123/bb6/actions/runs/44307926048), 2 [44325524818](https://github.com/FlareZ123/bb6/actions/runs/44325524818), and 3 [44326644032](https://github.com/FlareZ123/bb6/actions/runs/44326644032), preserving artifacts `d-root-stage3b1`, `d-root-stage3b2`, and `d-root-stage3b3`. Checkpoint 4 run [44327168149](https://github.com/FlareZ123/bb6/actions/runs/44327168149) ended with runner shutdown (exit 143) before preserving an artifact or producing a Lean diagnostic; the complete nineteenth reentry therefore remains unverified. Episode 20's E/E/E root transport remains pending.


## Blank-root continuation through the thirtieth exceptional section

The original-source D-start blank-root chain is now kernel-checked through the **eighteenth exceptional reentry**. The twelfth and thirteenth reentries were previously verified in CI [42089877845](https://github.com/FlareZ123/bb6/actions/runs/42089877845) and [42306192563](https://github.com/FlareZ123/bb6/actions/runs/42306192563). The earlier root audit [43394857303](https://github.com/FlareZ123/bb6/actions/runs/43394857303) compiled the fourteenth, fifteenth, and sixteenth reentries before runner shutdown; the dedicated stage-2b16 run [43534820371](https://github.com/FlareZ123/bb6/actions/runs/43534820371) independently recompiled episode 16. Stage-2b17i [43760695437](https://github.com/FlareZ123/bb6/actions/runs/43760695437) compiled `blank_seventeenth_reentry`, and stage-2b17j [43761344093](https://github.com/FlareZ123/bb6/actions/runs/43761344093) compiled its E7 escape. The eighteenth split checkpoints [44078315654](https://github.com/FlareZ123/bb6/actions/runs/44078315654), [44288454765](https://github.com/FlareZ123/bb6/actions/runs/44288454765), and [44289033894](https://github.com/FlareZ123/bb6/actions/runs/44289033894) respectively compiled the arithmetic certificate, `blank_eighteenth_exception`, and `blank_eighteenth_reentry`, with the standard-axiom gate passing. Episodes 19–30 and `Seed31Probe` remain unverified; the finite prefix is not an all-time nonhalting decision.

The monolithic eighteenth-stage attempt [43844908990](https://github.com/FlareZ123/bb6/actions/runs/43844908990) was cancelled while its compile step was in progress; it produced no artifact and no Lean diagnostic. The replacement split workflow [agent2-d-root-stage3a-split.yml](../../.github/workflows/agent2-d-root-stage3a-split.yml) is now fully successful: stage 1 [44078315654](https://github.com/FlareZ123/bb6/actions/runs/44078315654) compiled the arithmetic certificate, stage 2 [44288454765](https://github.com/FlareZ123/bb6/actions/runs/44288454765) compiled the authentic-root lift, and stage 3 [44289033894](https://github.com/FlareZ123/bb6/actions/runs/44289033894) compiled the E/B reentry. The corrected source pin is mathematical source `20509b53af45edce5b8a145e8714245d3d225cdd` plus proof-extension snapshot `2dcc75abcf2e0ca06c877336fad1d2d8d07e0abd`. The chain is verified through episode 18; episodes 19–30 and `Seed31Probe` remain unverified. This finite prefix is not an all-time nonhalting decision.

### Remaining submitted chain

Episodes 17 and 18 are source-verified; the source-connected Lean submissions for episodes 19–30 remain to be audited:

| Episode | DRegular sections from previous reentry | Exceptional source | t mod 27 | Submitted original-source continuation |
|---:|---:|---|---:|---|
| 17 | 2,656 | L(9t+7,7,1) | 6 | E/E/A three-return escape; rejoin L(512u+119,3,2) (source-verified in CI 43760695437) |
| 19 | 9,780 | L(9t+10,9,1) | 12 | E/A, parameter 2; rejoin pure unary L(64t+113,0,0) |
| 20 | 2,040 | L(9t+7,5,1) | 4 | E/E/E escape; rejoin L(8k+9,8,5) |
| 21 | 12,588 | L(9t+4,8,1) | 6 | E/B, parameter 6; rejoin L(64t+33,1,5) |
| 22 | 730 | L(9t+7,8,1) | 14 | E/E packet (192u+161,2,13); B normalization, then E-one rejoin |
| 23 | 3,636 | L(9t+4,2,1) | 21 | B-general rejoin L(64t+21,1,5) |
| 24 | 4,510 | L(9t+7,6,1) | 17 | E/E packet (192u+161,2,9); B normalization, then A-zero rejoin |
| 25 | 1,718 | L(9t+4,8,1) | 16 | E/B, parameter 6; rejoin L(64t+33,1,5) |
| 26 | 8,516 | L(9t+10,8,1) | 25 | E/A packet (24t+21,0,16); A-one rejoin to pure unary |
| 27 | 1,684 | L(9t+7,9,1) | 8 | E/E packet (192u+161,2,15); B normalization, then A-zero rejoin |
| 28 | 2,590 | L(9t+4,9,1) | 23 | E/B, parameter 7; rejoin L(64t+35,1,5) |
| 29 | 6,443 | L(9t+10,6,1) | 22 | E/A packet (24t+21,0,12); A-zero rejoin to pure unary |
| 30 | 2,613 | L(9t+10,8,1) | 22 | E/A packet (24t+21,0,16); A-one rejoin to pure unary |

Here `u=(t-2)/3` in the E/E rows. `BlankSeventeenthRejoin.lean` is source-verified in CI 43760695437, `ExceptionalE7ThirdReturnEscape.lean` in CI 43761344093, and `BlankEighteenthRejoin.lean` in CI 44289033894. The remaining modules for episodes 19–30 are submissions until their staged audit succeeds; `ExceptionalE7SecondSafe.lean` and `ExceptionalEPacketClosure.lean` supply shared branches.

### Verification workflow and next root question

The manual/reusable workflow [agent25-eleventh-root.yml](../../.github/workflows/agent25-eleventh-root.yml) carries compiled `.olean` files and the accumulated audit log through separate checkpoint runs. The successful stage-2a run [43408948256](https://github.com/FlareZ123/bb6/actions/runs/43408948256) uploaded `d-root-stage2a`; the dedicated stage-2b16 run [43534820371](https://github.com/FlareZ123/bb6/actions/runs/43534820371) certified episode 16. Stage-2b17i [43760695437](https://github.com/FlareZ123/bb6/actions/runs/43760695437) compiled the seventeenth root reentry, and stage-2b17j [43761344093](https://github.com/FlareZ123/bb6/actions/runs/43761344093) compiled its E7 escape. The split stage-3a checkpoints [44078315654](https://github.com/FlareZ123/bb6/actions/runs/44078315654), [44288454765](https://github.com/FlareZ123/bb6/actions/runs/44288454765), and [44289033894](https://github.com/FlareZ123/bb6/actions/runs/44289033894) now verify episode 18 through the E/B reentry. The monolithic stage-3b run [44289702591](https://github.com/FlareZ123/bb6/actions/runs/44289702591) ended with runner shutdown (exit 143) before any Lean diagnostic. The replacement split audit passed checkpoints 1 [44307926048](https://github.com/FlareZ123/bb6/actions/runs/44307926048), 2 [44325524818](https://github.com/FlareZ123/bb6/actions/runs/44325524818), and 3 [44326644032](https://github.com/FlareZ123/bb6/actions/runs/44326644032), preserving artifacts `d-root-stage3b1`, `d-root-stage3b2`, and `d-root-stage3b3`. Checkpoint 4 run [44327168149](https://github.com/FlareZ123/bb6/actions/runs/44327168149) ended with runner shutdown (exit 143) before preserving an artifact or producing a Lean diagnostic; the complete nineteenth reentry therefore remains unverified. Resume checkpoint 4 from the successful `d-root-stage3b3` artifact. Continue stages 3c–5e only from successful predecessor artifacts, keeping the mathematical source pinned at `20509b53af45edce5b8a145e8714245d3d225cdd`. `BlankTwentyFirstRejoin.lean` remains explicitly compiled before `BlankTwentySecondRejoin.lean`, which imports it.

The probe `Seed31Probe.lean` is a diagnostic computation over up to 1,024,000 DRegular transitions. It reports the first exceptional state found, its residue modulo 59049, q, b, and whether the next transition is undefined. Its output is not itself a proof. The next mathematical step is to certify the observed first-exit count and state with `DRegularFast.fastRun_correct`, lift that prefix through `DRegularSource`/`ObsEq`, and compose only the source theorem matching the actual state.

In particular, do not assume the q=4 target `L(59049*m+44494,4,1)` is reached: the current `t30 mod 27 = 22` certificate does not determine `t30 mod 81`. The one-step regular-model preimage calculation in [Q4RegularPreimages.md](../agent2-root-language-exit/Q4RegularPreimages.md) is a constraint, not a blank-root path. The separate conditional exception-41 candidate with `k41 ≡ 76 (mod 81)` is covered by Agent35's source-certified `P2K4Source.close_one` subfamily `k=27t+22`; this closes that particular model candidate, not the entire `k ≡ 4 (mod 9)` family or the independent `k ≡ 7 (mod 9)` family. Neither conditional packet closure proves blank-root reachability.

The chain is a finite ancestry result. It does not establish that the D machine runs forever, decide that holdout, or improve either BB(6) bound.


## Conditional continuation from seed34 through exception38 (submitted; CI pending)

Two new source-composition modules extend the candidate blank-root chain from the exception-33 unary seed through five further DRegular first stops and their matching original-source reentries:

- [BlankThirtyFourthToThirtySixthRejoin.lean](BlankThirtyFourthToThirtySixthRejoin.lean)
- [BlankThirtySeventhToThirtyEighthRejoin.lean](BlankThirtySeventhToThirtyEighthRejoin.lean)

The exact 512-block DRegularFast certificate targets and reused source-return families are:

| Exception | Regular transitions | First-stop section | a mod 59049 | Parameter residue | Source return |
|---:|---:|---|---:|---:|---|
| 34 | 12,638 | L(9*t34+4,6,1) | 55,039 | t34=(a-4)/9, t34 mod 27=13 | ExceptionalBGeneral.exceptional_EB_general with p=4; rejoin L(64*t34+29,1,5) |
| 35 | 335 | L(9*t35+4,9,1) | 54,265 | t35=(a-4)/9, t35 mod 27=8 | E/B general with p=7; rejoin L(64*t35+35,1,5) |
| 36 | 615 | L(9*t36+10,7,1) | 27,469 | t36=(a-10)/9, t36 mod 27=0 | Agent37TwelfthPacket.two_returns; rejoin L(64*t36+91,3,2) |
| 37 | 2,348 | L(9*t37+4,6,1) | 50,584 | t37=(a-4)/9, t37 mod 27=4 | E/B general with p=4; rejoin L(64*t37+29,1,5) |
| 38 | 1,341 | L(9*t38+10,1,1) | 24,670 | t38=(a-10)/9, t38 mod 27=13 | Agent25E3SourceBridge.q1b1_regular_rejoin_E; rejoin L(64*t38+49,6,0) |

Each submitted segment proves a DRegular.run endpoint and DRegular.next = none at the following transition, then lifts the regular segment through Agent25RootChain.extend_regular. The exception closures reuse existing original-source theorems rather than re-proving their macro traces. The composed blank_thirty_eighth_reentry therefore reaches the canonical section seed39 = L(64*t38+49,6,0), conditional on the exception-33 root prefix and all earlier staged source lifts.

The artifact-reusing manual workflow [agent37-root-exceptions34-38.yml](../../.github/workflows/agent37-root-exceptions34-38.yml) consumes both the stage-5 d-root-seed31-audit artifact and the successful seed31-first-stop-certificate artifact, then compiles these two modules and checks for forbidden sorryAx/native_decide dependencies. It has no push trigger. Until that audit succeeds, these files and the five exact signatures are submitted candidates, not kernel-verified results. In particular, this finite conditional continuation neither authenticates the still-pending episodes 19–30 nor proves that the D machine is nonhalting.


## November 20, 2026: current D-root frontier

### Episode 19: 64-block kernel-only candidate; preflight pending

The current NineteenthTail5684.lean uses the generic 64-step block
evaluator with kernel reduction: 5684=64*88+52, via
run_blockedWith 64 88 52 and decide. It prints axioms for tail5684_exact,
matching the stage-4a workflow's audit requirement.

NineteenthTerminalCertificate.lean then uses the small compositional join:
9780=4096+5684, DRegularFast.run_add 4096 5684 seed19,
block19_1_exact, and tail5684_exact. The stage-4b #print axioms
terminal9780_exact is the complete transitive audit, including the
64-block tail proof. This avoids re-running the entire 9,780-step
computation and makes the stage split meaningful.

The previous 32-block tail used native_decide and is superseded; it is not
acceptable as a kernel-only result.

CI run 44681991222 did not test either the previous fast32 candidate or
this new 64-block candidate. Its pinned extension ref f31592b2c6d490209e1473d150b42bbae710213d still used the old direct
run_add 4096+1588 proof. The failed job was terminated by a runner shutdown
signal at 05:38:02Z, without a Lean diagnostic; it is not evidence of a
mathematical or elaboration failure in the current source.

This 64-block version is a kernel-only proof candidate, not yet a verified
theorem: the current invocation could not run local Lean preflight because
the local execution boundary failed before running commands. Do not dispatch
CI as a substitute for that required preflight. After local preflight,
the reproducible stage-4a inputs are:
- stage=4a
- source_run_id=44326644032
- previous_artifact=d-root-stage3b3
- source_ref=20509b53af45edce5b8a145e8714245d3d225cdd
- previous_extension_ref=0ddab8f895b4f202bfdee684d28b7ae62a6b3d8e
- extension_ref=fdb8f0803bd26e82791712907b6169c647ec001e

These inputs resume from the successful stage-3b3 artifact and pin the
exact predecessor and new proof extension. The workflow is dispatched from
main, so recheck its current inputs/audit gate before running. After stage
4a succeeds and preserves d-root-stage3b4a, run stage 4b from that artifact
with the same source and extension pins.

The source-root lift and episode-19 exceptional reentry files are prepared
but not verified. The E/A packet issue is no longer a current proof defect:
commit e7009d5 fixed the q−1 successor case, and CI run
[43394857303](https://github.com/FlareZ123/bb6/actions/runs/43394857303)
printed [propext, Quot.sound] for exceptional_EA_packet before the
larger audit was externally shut down at the sixteenth root. The earlier
43391359969 failure is from the pre-fix source. Run
[44289702591](https://github.com/FlareZ123/bb6/actions/runs/44289702591)
also ended in runner shutdown without a Lean diagnostic.

### Conditional episode-41 packet closure

The corrected conditional DRegular trace reaches
\(L(9t_{41}+7,7,1)\), whose source-specific EEE escape yields the p=2
packet \(M(512u_{41}+257,4,2;0\,1^6)\). With
\(k_{41}=81s+76=27(3s+2)+22\) and \(q=7=3\cdot2+1\), this is covered by
P2K4SourceReentry.close_one_regular_reentry. The wrapper and its
root-prefix composition were kernel-audited in CI run
[43391093227](https://github.com/FlareZ123/bb6/actions/runs/43391093227),
with [propext, Quot.sound].


Evidence status: the #41 first-stop identification is still a model-only
computational candidate, not a kernel-certified first-stop theorem.
The actual seed39 used by Seed39Probe.lean is
\(L(64t_{38}+49,6,0)\), supplied by
BlankThirtySeventhToThirtyEighthRejoin.lean. Seed39Probe evaluates
firstExceptionFromSeed39 using firstStopBlocks with a 2,000-block cap
(1,024,000 regular transitions). Its soundness theorem is conditional on
the bound firstExceptionFromSeed39.1 < 1024000; that bound is not proved
in the file, and the reported #eval output is not stored as a certificate.
The manual workflow agent37-root-exceptions34-38.yml has no runs and does
not compile Seed39Probe. Therefore the reported residue
\(L(9t_{41}+7,7,1)\), \(t_{41}\equiv76\pmod{81}\), must be treated as a
computational hypothesis. The source closure below is a verified
conditional implication for that packet if the candidate is confirmed.

Do not confuse this actual root seed39 with
DRegularFirstExit.seed39_exception, which starts from the separate toy
state \(L(39,0,0)\).

Unfolding the q=7 endpoint normalizer gives the next regular seed
\(L(4096t+3461,4,0)\), where \(t=3s+2\), equivalently
\(L(12288s+11653,4,0)\). This closes the specific #41 packet candidate,
not its blank-root reachability: the upstream episodes 19–38 remain
unverified, and the first exceptional return from this new seed has not
been computed.

The broader p=2 classification remains incomplete. The K=4 wrapper covers
only \(k=27t+22,\ q=3u+1\). The raw P2K7Source family covers
\(k=27t+25\) across q mod 3 and compiled in CI run
[42519761689](https://github.com/FlareZ123/bb6/actions/runs/42519761689),
but its regular-section wrapper is not yet present. Other k≡4,7 (mod 9)
subfamilies and deeper 3-adic cylinders remain; see the packet-shift
dossier for the exact source families.

### General safe E-exit candidate

ExceptionalESafeReentry.lean and ExceptionalESafeCanonical.lean
remain submitted proof candidates, not compiled theorems. The canonical
module now contains its own private `e_output_packet` shape lemma, removing
the known unresolved identifier from the source. This is a source-level
repair only: no Lean compile or axiom audit has been completed because the
local runtime is unavailable. The q=5 episode-20 root input already has a
separate EEE-to-P4 escape, so this general safe-E candidate is not a
prerequisite for that particular root step.



## November 23, 2026: revised nineteenth-root compilation and episode-20–30 handoff

This section supersedes the older episode-19 "64-block candidate; preflight pending" workflow note above.

### Episode 19: one-process source-reentry certificate (CI pending)

The large `NineteenthTail5684.olean` and `NineteenthBlock3.olean` imports repeatedly ended in runner shutdown when used by separate terminal modules. The current alternative is `NineteenthReentryComplete.lean`, which imports the smaller `NineteenthBlock2` closure, recomputes the final 1,588-step fast block in the same Lean process, and composes the existing exact certificates:

- `block19_1_exact`: 4,096 steps;
- `block19_2_exact`: 4,096 steps;
- `terminal1588_exact`: 1,588 steps.

It then proves `terminal9780_exact`, the authentic blank-root nineteenth exception, and the original-source E/A packet reentry `blank_nineteenth_reentry` in that same module. The last theorem targets the pure-unary section `L(64*t19+113,0,0)`.

The focused stage-4d CI run is [45161497546](https://github.com/FlareZ123/bb6/actions/runs/45161497546), using source snapshot `20509b53af45edce5b8a145e8714245d3d225cdd`, extension `fdea1e851d50520f40835816319c88d14dc1c481`, predecessor artifact `d-root-stage3b3` from run `44326644032`, and predecessor extension marker `0ddab8f895b4f202bfdee684d28b7ae62a6b3d8e`. **At the time of this update the run is still in progress; do not treat any theorem in the new module as CI-verified until this run succeeds and its axiom audit is checked.**

### Episode 20–30 continuation

The staged workflow `agent25-eleventh-root.yml` now starts episode 20 at stage 3c from artifact `d-root-stage3b4d`, requiring `NineteenthReentryComplete.olean`, `ExceptionalE7ThirdReturnEscape.olean`, and `DRegularFast.olean`. It checks out a separately pinned proof extension and overlays the current episode 20–30 source modules, while retaining the exact original source snapshot.

The twentieth 2,040-step regular prefix and the 22nd–26th regular prefixes now use `DRegularFast.fastRun_correct` with explicit canonicality proofs rather than direct large `DRegular.run := by decide` evaluations. The extension snapshot prepared for this continuation is `cb2d702017eb5b04275df0b39480ed27075871d5`; source remains `20509b53af45edce5b8a145e8714245d3d225cdd`.

If stage 4d succeeds, dispatch stage 3c with its run ID and artifact `d-root-stage3b4d`, then proceed sequentially through stages 3d/3e, 4a–4g, and 5a–5e. The final stage produces the Seed31 probe artifact `d-root-seed31-audit`, which feeds the existing Seed31 first-stop certificate workflow and then the conditional 34–38 / Seed39 probe workflow.

This is a finite conditional trajectory program. Even a successful Seed31/Seed39 probe is not, by itself, a global proof of halting or nonhalting and does not determine BB(6).
