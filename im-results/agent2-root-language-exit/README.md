# Cryptid D: first regular-language exits of four blank-derived arithmetic seeds

**Status: arithmetic-model and finite source-reentry dossier; global D halting remains unresolved.** An independent Lean development now formally certifies a concrete halting cylinder for this exact D-start machine. The missing theorem is authentic blank-root reachability of that cylinder (or another certified halting class), not an all-time nonhalting invariant. The existing [Agent 37 word-level programme](../agent37-root-language-pilot/README.md) and genuine-root original-source reentries from Agent 35 and Agent 37 remain useful finite-prefix machinery, but they must be evaluated against the halting-reachability problem.

## External halting cylinder: known target, missing reachability

The exact machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` has two independent external Lean treatments. Google DeepMind's [Cryptids #490 stack-reduction proof](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean) identifies it as #85 restarted from D and mirrored, proves a closed pair-stack reduction, and proves the seven-step blank entry into that system. Separately, [@-d's Lean proof](https://github.com/int-y1/proofs/blob/1929f57df4dd7afcc11c3f458e20526fd1f991e0/BusyLean/Individual/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---.lean) defines the exact transition table, proves `reach_9_nil : c₀ ⊢* A 9 []` in 36 raw steps, and proves `halts_A_mod_3_pow_108`: every
`A(3^108*k + C, [])` halts, where
`C=1975700577069254261393123959451562008800234946348086`.

The corresponding 108-step E/B word is recorded in the [resource note](../../resources/2026-11-20-cryptid-D-halting-cylinder.md). This is a proved halting target, not a proof that the orbit from `A(9, [])` reaches it. The wiki reports 2,728,570 simulated A-states with a closest 21/108 match and estimates a halting time around `10^10^38.1`; those are empirical/heuristic only. The initial configuration correspondence is already established by the source encoding: `DRegularSource.sourceSection (9,0,0) = init (List.replicate 7 true)`, and `init` supplies the two leading unary bits, giving the same nine-one F-state section as `A(9,[])` after symbol/state encoding. The remaining bridge is transition-level: identify how each repository DRegular/source-reentry segment updates the arbitrary suffix `r` and matches the external E/B/A macro. Do not interpret a finite reentry chain as evidence of nonhalting.

## 3-adic synchronization already proved on canonical A-sections

For a DRegular state `s=⟨a,q,b⟩`, the source suffix is `r=(01)^q1^b`. The canonicality condition `q>0 ∨ b=0` ensures that `r` is empty or begins with 0, matching the side condition of the external `A(n,r)` notation. The initial state `L(9,0,0)` is exactly the empty-suffix A(9,[]) section after the two implicit unary bits in `init`.

The repository already proves the 3-adic prefix-synchronization law on this regular suffix language. `DRegularShift.run_shift` says that a successful k-step run from `s` is synchronized with the run from the `3^k*p` input lift, and the output parameter shifts by `8^k*p`; the model theorem also matches first-exit behavior. `DRegularSourceShift.lifted_original_run` and `paired_original_run` transport successful runs to the original machine. These were verified in CI runs [41872704046](https://github.com/FlareZ123/bb6/actions/runs/41872704046) and [41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993), with the eleven-row source contract audited in [41712102615](https://github.com/FlareZ123/bb6/actions/runs/41712102615); the recorded axiom profiles use only standard axioms.

The new `ARegular3AdicBridge.lean` is a small, not-yet-preflighted exposition wrapper that names the physical section `ASection(n,r)` and states the regular-suffix result directly. This gives the source-certified 3-adic shift analogue for DRegular section paths on the canonical regular language. It does **not** cover arbitrary suffixes or automatically bridge every exceptional exit, and the exact first-return identification of `DRegular.duration` with the external A-macro remains to be checked. The [target-C DRegular probe](./halting-cylinder-DRegular-probe.md) compares the external Lean proof's actual checkpoints: its first ten A-macro transitions reach `A(D1,(01)^4 1)`, exactly the DRegular first-exit state `L(D1,4,1)`; the next ten reach `A(D2,01011101010111)`, whose suffix is outside the regular language. The q=4 E/E plus p2 source closure returns to a later regular section and therefore is an accelerator, not the next A-macro transition. This identifies the missing task as tracking intermediate arbitrary-suffix A-states, not comparing raw DRegular branch labels with the 108-letter word. The next structural task is to compose the shift law with the existing source-reentry theorems across those exits, or extend the model to arbitrary `r`, then use that complete orbit description to attack reachability of the 108-step halting cylinder.

## Mathematical object and exact statement

For the D machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, use the prepared physically blank-left F/0 regular section
`L(a,q,b)=I_a((01)^q1^b)`, with `a≥2`, `q≥1` and `b≥0`; the canonical `q=0` case has `b=0`.

`DRegularFirstExit.lean` defines an explicit total arithmetic successor `step : S → Option S` using the B, A and E branch table in Agent 37's already source-connected eleven-row model. It returns `none` for the E sector `a≡1 (mod 3), q≥1,b=1`, which is a **regular-language exit**, not a machine halt. It takes care to absorb the trailing `b` ones into the unary count for B with `q=1`, so physically identical tapes share a canonical state.

Let `run n (some s)` iterate the arithmetic partial successor `n` times. The standalone Lean kernel proves the following four exception certificates; each reported index is the **input section**, beginning at index zero. The succeeding abstract `step` returns `none`.

| Canonical starting section | First exception index | `a mod 243` | `q` | `b` | `a` bit length | Next prepared packet |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `I_5` | 1,711 | 211 | 5 | 1 | 2,424 | `M(8k+5,0,10;0 1^6)` |
| `I_9` | 8,394 | 157 | 6 | 1 | 11,882 | `M(8k+5,0,12;0 1^6)` |
| `I_15` | 9,458 | 121 | 9 | 1 | 13,388 | `M(8k+5,0,18;0 1^6)` |
| `I_39` | 7,611 | 46 | 7 | 1 | 10,776 | `M(8k+5,0,14;0 1^6)` |

In each row `a=3k+4` at the exception input. Lean also proves **every preceding arithmetic section remains in the regular domain** via an arbitrary-time prefix theorem `no_early_exit` and the four individual `seed*_prior` theorems. This avoids presenting a finite sample or empirical last-row observation as a quantified earlier-exit certificate. The numeric `seed*_exception` and `seed*_exit` statements use `by decide` and have **no axioms**. `seed*_prior` depends only on `propext`; local Lean 4.36.0-rc2 completed all checks. The kernel does *not* prove that this arithmetic model faithfully describes all true blank-origin physical returns.

The separate `check_first_regular_exit.py` independently represents each state as its full canonical finite binary word, imports the existing Agent 37 `macro_engine.py`, and compares every model transition through each reported first exit. It checks that the actual next **word-level macro** is precisely `0 1^(2q) 0 1^6`, and records reproducible SHA-256 digests of the section sequences. Agreement provides an interpreter cross-check, not an additional original-source machine proof.

## Immediate exit closures and provenance boundary

For the first three rows, the displayed packet has `p=10,12,18`; all satisfy `p mod 3 ∈ {0,1}`. The existing **original six-state source-certified** theorem [Agent2 PacketSafeReentry.all_safe_packets_regular](../agent2-packet-shift/README.md) therefore gives a designated finite reentry into regular `L`, for each packet and arbitrary unary length `a≥4`. This supplies an exact source family for the *prepared packet*; applying it to the computed blank-derived sequence remains conditional on lifting the intervening arithmetic model to the actual blank trajectory.

For the fourth row `a mod 243=46`, so the post-E packet unary length `8k+5 ≡36 (mod 81)` is divisible by three. It is an **A-terminal**, with packet `M(3u+3,0,14;0 1^6)`. The pre-existing all-parameter, source-verified [Agent35 APacketGeneral.source_a_packet_regular](../agent35-d-sixth-rejoin/APacketGeneral.lean) applies directly with `q=0,r=4`: the prepared packet returns to `L(8u+43,3,2)`. Its exact primitive duration specializes to `12u²+145u+474`, including four `111` tokens and the terminal `110111`. An independent literal 12-rule six-state interpreter checked this duration, full right suffix and physical blank-left first return for `0≤u≤19`; these 20 cases are regression evidence only. This A packet reentry mechanism was already established by Agents 31 and 35 and must not be counted as new mathematical novelty.

These results prove that **all four first arithmetic-language exceptions have known prepared, original-source regular reentries**. They do not prove a later exception cannot lead to an F/1 halt or a no-event E3 core, nor do they certify any long authentic blank-root survival interval. The previously source-certified [Agent 37 twelfth blank-root exceptional return](../agent37-d-timing-cocycle/README.md) already handles an instance of the same q=7 A packet mechanism, and should be reused rather than independently re-proving its raw machine path.

## Highest-value outstanding proof

The D-start blank-root chain is now original-source verified through the eighteenth exceptional reentry. The successful stage-2a artifact covers episodes 14–15; the dedicated stage-2b16 **64-step evaluator** run [CI 43534820371](https://github.com/FlareZ123/bb6/actions/runs/43534820371) independently recompiles the sixteenth terminal and root exception/reentry, preserving `d-root-stage2b16`. The staged stage-2b17i run [CI 43760695437](https://github.com/FlareZ123/bb6/actions/runs/43760695437) compiles `blank_seventeenth_reentry` with axiom profile `[propext, Classical.choice, Quot.sound]` and preserves `d-root-stage2b17i`; stage-2b17j run [CI 43761344093](https://github.com/FlareZ123/bb6/actions/runs/43761344093) compiles `exceptional_EEE_escape` with `[propext, Quot.sound]` and preserves `d-root-stage2b17j`. Stage-2b17i was compiled at source `b3cc897d85ff6c69ca29a24be2aa3bf6931e13f7`; stage-2b17j used `20509b53af45edce5b8a145e8714245d3d225cdd`. The eighteenth proof is split across `EighteenthArithmetic.lean`, `EighteenthRootPrefix.lean`, and `BlankEighteenthRejoin.lean`: arithmetic checkpoint [44078315654](https://github.com/FlareZ123/bb6/actions/runs/44078315654), authentic-root lift `blank_eighteenth_exception` [44288454765](https://github.com/FlareZ123/bb6/actions/runs/44288454765), and E/B packet reentry `blank_eighteenth_reentry` [44289033894](https://github.com/FlareZ123/bb6/actions/runs/44289033894) all succeeded and preserved their artifacts. The latter two runs used mathematical source `20509b53af45edce5b8a145e8714245d3d225cdd` and proof-extension snapshot `2dcc75abcf2e0ca06c877336fad1d2d8d07e0abd`; the workflow's standard-axiom and forbidden-axiom gates passed. The monolithic stage-3b run [44289702591](https://github.com/FlareZ123/bb6/actions/runs/44289702591), the earlier split checkpoint-4 run [44327168149](https://github.com/FlareZ123/bb6/actions/runs/44327168149), both attempts of the first replacement run [44597342451](https://github.com/FlareZ123/bb6/actions/runs/44597342451), the combined-composition retry [44680837979](https://github.com/FlareZ123/bb6/actions/runs/44680837979), and the first isolated-tail attempt [44681315050](https://github.com/FlareZ123/bb6/actions/runs/44681315050) all ended with runner shutdown (exit 143) before any Lean diagnostic. These are execution failures, not Lean counterexamples. The replacement split audit passed checkpoints 1 [44307926048](https://github.com/FlareZ123/bb6/actions/runs/44307926048), 2 [44325524818](https://github.com/FlareZ123/bb6/actions/runs/44325524818), and 3 [44326644032](https://github.com/FlareZ123/bb6/actions/runs/44326644032), preserving artifacts `d-root-stage3b1`, `d-root-stage3b2`, and `d-root-stage3b3`. The current endpoint-composition replacement uses the existing stages 4a and 4b. Stage 4a run [44681991222](https://github.com/FlareZ123/bb6/actions/runs/44681991222) pinned the obsolete proof-extension snapshot `f31592b2c6d490209e1473d150b42bbae710213d` and ended with runner shutdown before a Lean diagnostic; it did **not** test the current 64-block candidate. The current `NineteenthTail5684.lean` uses `run_blockedWith 64 88 52` and kernel `decide`; it is still unverified. The intended 9,780-section endpoint composition is in `NineteenthTerminalCertificate.lean`, whose transitive `#print axioms terminal9780_exact` audits the tail. The mathematical source remains `20509b53af45edce5b8a145e8714245d3d225cdd`; predecessor artifact `d-root-stage3b3` is run [44326644032](https://github.com/FlareZ123/bb6/actions/runs/44326644032), with previous extension marker `0ddab8f895b4f202bfdee684d28b7ae62a6b3d8e`. Agent 37 reports a working local Lean runtime and has been asked to preflight the exact current source closure, coordinating with Agent 35. Only after full local preflight should the existing stage 4a/4b workflow be used, followed by authentic-root lift 5 and original-source reentry 6. The complete nineteenth reentry remains unverified; episodes 19–30 and Seed31 remain unverified.

### Seed31: conditional exact arithmetic first stop

The submitted [BlankThirtiethRejoin.lean](../agent37-d-timing-cocycle/BlankThirtiethRejoin.lean) defines the next pure-unary seed as
`seed31 = L(64*t30+117,0,0)`.
An exact BigInt replay of the DRegular recurrence, using independent 512-step and 256-step 3-adic block sizes, gives:

- `t30 mod 81 = 22`; seed31 has 180,684 bits and `seed31.a mod 81 = 67`.
- The first undefined DRegular successor occurs after **12,267** regular transitions, at `L(a,8,1)` with `a mod 59049 = 39637`, `a mod 81 = 28`, and `t31=(a-10)/9 mod 27 = 2`.
- This is not the conditional q=4 cylinder `L(59049*m+44494,4,1)`. The q=4 local closure remains a valid source theorem, but this computed seed31 does not enter it.

This is an exact arithmetic result for the submitted seed31, not a source-certified original-machine root theorem: its dependency on the still-unverified episodes 19–30 root chain is essential. The detailed replay, downstream arithmetic signatures through exception 38, and exact limitations are in [seed31-38-exact-replay.md](seed31-38-exact-replay.md).

### Candidate original-source continuation after the q=8 first stop

The q=8 E/A exception has an existing source return. The E-first packet has p=16=3*5+1, so [EFirstAPacket.exceptional_EA_packet](../agent2-packet-shift/EFirstAPacket.lean) followed by [AOnePacketBoundarySource.a_p1_boundary](../agent2-packet-shift/AOnePacketBoundarySource.lean) returns to the pure-unary seed `L(64*t31+117,0,0)). The candidate root composition is [BlankThirtyFirstRejoin.lean](BlankThirtyFirstRejoin.lean).

The next arithmetic first stop is after 6,106 regular transitions, at `L(9*t32+4,1,1)`, with `t32 mod 27 = 5`. Agent 25's [E3SourceRejoin.lean](../agent25-cryptid-doublezero/E3SourceRejoin.lean) proves the physical two-far-right-blank ObsEq bridge and the q=1,b=1 branch-A return to `L(64*t32+27,0,0)`; Agent 25 reports this branch compiled with only standard axioms. [BlankThirtySecondRejoin.lean](BlankThirtySecondRejoin.lean) composes that shared bridge with the conditional blank-root prefix. The same module also contains branch-B and branch-E reentries for the other two residues of the q=1,b=1 family; branch-E closes the exception-38 tail13 output to `L(64*t38+49,6,0)` via the explicit one-blank ObsEq transport. The all-residue theorem `q1b1_rejoins_regular` has now compiled successfully in [CI run 43420030637](https://github.com/FlareZ123/bb6/actions/runs/43420030637), with only `[propext, Quot.sound]` in its kernel audit. This closes the q=1,b=1 E-section family at source level, but does not certify the blank-root prefix to any of these candidate sections.

From seed33, the exact DRegular replay reaches exception 33 after 9,276 transitions at `L(27u+7,5,1)`, with `a mod 59049 = 49579` and `t=3u`. Agent 25's [Exception33Q5Rejoin.lean](../agent25-cryptid-doublezero/Exception33Q5Rejoin.lean) supplies the prepared-section original-source EAllDouble(q=4) → E-three → A-code return to `L(512u+129,0,0)`. The corrected source bridge passed current-main CI [run 44740066064](https://github.com/FlareZ123/bb6/actions/runs/44740066064); all five audited declarations have only `[propext, Quot.sound]`, no `sorryAx` or `native_decide`, and artifact `agent25-e3-source-bridge` ID `14628939997`. Its total duration algebraically simplifies to `57036*u^2 + 22057*u + 2222 + CryptidA.wordCost(256*u+43, [false,false,true,true,false,true,true])`. The proof repairs and duration expression are recorded in the [Agent 25 dossier](../agent25-cryptid-doublezero/README.md). New Agent 2 [BlankThirtyThirdRejoin.lean](BlankThirtyThirdRejoin.lean) composes that return with the conditional blank-root prefix through seed33. **This root composition is submitted but not yet kernel-verified**; it remains conditional on source certification of episodes 19–30 and the preceding Seed31/32 lifts.

The exact first-stop signature, unconditional first-stop corollary, t30 residue theorem, and two blank-root reentry modules have been submitted in Lean. They are **not yet kernel-verified**. The artifact-reusing manual workflow [.github/workflows/agent2-seed31-first-stop-certificate.yml](../../.github/workflows/agent2-seed31-first-stop-certificate.yml) now compiles the certificate, q=8 reentry, Agent 25's q=1 bridge, and q=1 reentry in dependency order. It requires the completed `d-root-seed31-audit` artifact's `source_run_id`; keep the source revision pinned to `2da159d86fa86d813bdfbc54e38e3ec9c75b6e69`. It is manual and does not run on every commit.

### Next discriminating work

1. Continue the original-source audit from episode 19 and produce the pinned `d-root-seed31-audit` artifact. The eighteenth split proof is complete: [44078315654](https://github.com/FlareZ123/bb6/actions/runs/44078315654) certifies the arithmetic checkpoint, [44288454765](https://github.com/FlareZ123/bb6/actions/runs/44288454765) certifies `blank_eighteenth_exception`, and [44289033894](https://github.com/FlareZ123/bb6/actions/runs/44289033894) certifies `blank_eighteenth_reentry`. The nineteenth arithmetic checkpoints 1 [44307926048](https://github.com/FlareZ123/bb6/actions/runs/44307926048), 2 [44325524818](https://github.com/FlareZ123/bb6/actions/runs/44325524818), and 3 [44326644032](https://github.com/FlareZ123/bb6/actions/runs/44326644032) are preserved. The only stage-4a attempt [44681991222](https://github.com/FlareZ123/bb6/actions/runs/44681991222) used the older extension ref `f31592...` and ended in runner shutdown without a Lean diagnostic; it did not test the current candidate. The current [NineteenthTail5684.lean](../agent37-d-timing-cocycle/NineteenthTail5684.lean) candidate uses `5684=64*88+52`, `run_blockedWith 64 88 52`, and kernel `decide`; stage 4b composes `run_add 4096 5684` through this tail and audits `terminal9780_exact` transitively. Both files remain uncompiled pending local Lean preflight. After preflight, use stage=4a with source_run_id=44326644032, previous_artifact=`d-root-stage3b3`, source_ref=`20509b53af45edce5b8a145e8714245d3d225cdd`, previous_extension_ref=`0ddab8f895b4f202bfdee684d28b7ae62a6b3d8e`, extension_ref=`fdb8f0803bd26e82791712907b6169c647ec001e`. Then run stage 4b from `d-root-stage3b4a`, stage 5 from `d-root-stage3b4b`, and stage 6 from `d-root-stage3b5`. Only the successful stage-6 artifact `d-root-stage3b` authenticates the nineteenth reentry. Without the full 19–30 audit, the Seed31 arithmetic is not connected to the authentic blank root.
2. Run the updated certificate workflow. First settle the exact t30 residue and 12,267-step q=8 first-stop theorem; then compile the q=8 E/A source return and q=1 physical two-blank bridge.
3. Kernel-check the exception-33 root composition in `BlankThirtyThirdRejoin.lean`. Its prepared-section E3 source dependency is now CI-certified in run [44740066064](https://github.com/FlareZ123/bb6/actions/runs/44740066064), but the root composition remains conditional on episodes 19–30 and the Seed31/32 lifts. Agent 37 has now supplied `BlankThirtyFourthToThirtySixthRejoin.lean` and `BlankThirtySeventhToThirtyEighthRejoin.lean`; together they reuse the q=6/q=9 E/B, q=7 E/A, and q=1,b=1 E returns to extend the conditional chain through seed39. Their manual artifact-reusing audit is `.github/workflows/agent37-root-exceptions34-38.yml`; it has not yet been dispatched. For exception 38, reuse Agent 25's compiled `q1b1_regular_rejoin_E` branch, which proves the one-trailing-blank ObsEq transport for `oppairs(6) ++ [false]`; the remaining task is kernel-checking and composing these returns with the source-certified root prefix.
4. Continue toward an inductive physical blank-root invariant or find the first genuinely reachable uncovered successor. A finite sequence of prepared-section reentries is not an all-time nonhalting decision.

The previous q=4 instructions remain relevant only for a root path that actually reaches `L(59049*m+44494,4,1)`; they must not be imposed on the q=8 Seed31 branch computed here. No conclusion about the D machine's eventual behavior, BB(6), or the exact Busy Beaver value follows from this intermediate work.

## Concrete P2 reset continuation candidate from L(24956,2,2)

The concrete double-B/A marker route in the Agent 37 dossier has intended
endpoint `L(24956,2,2)`: the two B edges preserve the suffix budget
`p=3`, so the A-marker quotient is `r=1`. The concrete proof was corrected in commit
`9918fe91715c86650d80d6042d3cee6a245a84a0`: the B endpoint and A input
both retain `p=3`, the A quotient is `r=1`, and the endpoint is
`L(24956,2,2)`. The correction is still uncompiled and awaits local
preflight and original-source CI. Do not
use the separate `L(24972,2,2)` arithmetic experiment as its continuation.

An independent simulation of the DRootL arithmetic step table from the intended
`L(24956,2,2)` endpoint gives, after 86 regular transitions,
`L(107283033157493534200791430928221345342090,5,1)`. Its unary
parameter is congruent to 23638 modulo 59049 and to 4 modulo 9, so it is
`L(3k+4,5,1)` with
`k=35761011052497844733597143642740448447362`. Since q=5 is at least
2 and is not 1 modulo 3, the submitted
`ExceptionalESafeCanonical.all_E_safe_reentry_canonical` theorem is the
appropriate next source closure.

The candidate
[`Seed24956SecondReentry.lean`](Seed24956SecondReentry.lean) attempts
to kernel-check the 86-step DRegular run with `by decide`, lift it to
the original machine using
`DRegularSourceShift.lifted_original_run`, and compose it with the
safe-E source theorem and the concrete reset route. It is uncompiled.
Acceptance requires: (1) repair and compile the p=3 concrete reset source
theorem; (2) locally preflight and compile the safe-E dependency; (3)
audit the transitive axioms of the composed theorem. This is a prepared
packet result only, not a blank-tape reachability claim.

## Infinite 3-adic second-return families (source composition uncompiled)

The candidate [`Seed24956FamilySecondReentry.lean`](Seed24956FamilySecondReentry.lean) strengthens the concrete reset instance to an infinite depth-one family. For every r≥0, the P2 reset packet with k=81r+61 and Q=0 source-returns to the exact regular section L(32768r+24956,2,2). The parameter identities are explicit: the P2 reset yields M(648r+493,0,6); the d=1 E-chain with h=54r+41 yields M(1728r+1313,2,3); two B edges with t=64r+48 yield M(12288r+9354,0,3); and the A marker with ka=4096r+3117 and quotient 1 yields endpointZero(32768r+24955), hence L(32768r+24956,2,2).

For the second return, choose r=3^87 s. The DRegular source-shift theorem transports the 86-step base run with shift parameter p=32768·3s: the input shift is 3^86 p=32768·3^87 s, while the output shift is 8^86 p=3·8^86·32768s. Thus the output remains an E exit of the form L(3k'+4,5,1), with k'=35761011052497844733597143642740448447362+8^86·32768s. The universal q=5 safe-E canonical closure then gives a second return to a canonical DRegular section for every s≥0.

A separate depth-three family is now composed in [`Seed24956Depth3SecondReentry.lean`](Seed24956Depth3SecondReentry.lean), using Agent 37's [`D3SecondReturnAlignment.lean`](../agent37-echain/D3SecondReturnAlignment.lean). Put
\[
s=202789636786509251933665269483979866281743+3^{87}v,\quad
k=729s+310,\quad Q=3.
\]
The exact source path is P2 reset → three guarded E calls → B → B → A, with
\[
h=54s+23,\quad t=4096s+1744,\quad k_A=64t+45.
\]
Its endpoint is
\[
L(8k_A+28,2,2)
 =L(24956+3^{87}(1315608+2^{21}v),2,2).
\]
This is exactly the 86-step input lift of L(24956,2,2) with shift parameter p=3(1315608+2^21v). The lifted DRegular orbit reaches the q=5 safe-E class with exit parameter
\[
k'=35761011052497844733597143642740448447362
   +8^{86}(1315608+2^{21}v),
\]
after which the universal safe-E canonical closure supplies a second source return.

Agent 37 reports that the arithmetic alignment and the standalone 86-step DRegular model family compile locally with only standard axioms. The new combined original-source wrapper is **not yet locally preflighted, compiled, or axiom-audited**. Both families are prepared-packet results only; neither establishes that a member is reached from the blank tape. Do not promote them to `results/` until the complete source closure is compiled and the transitive axiom profiles are checked.


## 2026-11-20: seven-step 3-adic shadow of the external D halting cylinder

See [the intermediate result](halting-cylinder-seven-step-shadow.md), [exact BigInt replay](halting-cylinder-shadow.mjs), and [uncompiled Lean source candidate](HaltingCylinderShadow.lean). The blank-derived DRegular model reaches a state L(C+3^7*p,0,0) after 2,640 transitions, with p congruent to 1 modulo 3. The existing shift theorem synchronizes seven further DRegular steps with the first seven external checkpoint states; the eighth branch differs. This is a finite 3-adic shadow, not entry into the 3^108 halting cylinder. The endpoint sieve is not a raw-trajectory exclusion because first-return/minimality remains open. The Lean candidate is not yet preflighted or CI-audited.

The later source-certified seventeenth/eighteenth reentries also miss the corresponding external j=2/j=1 checkpoint families at mod-3 level; see the reentry table in [the intermediate note](halting-cylinder-seven-step-shadow.md) and the candidate [KnownCylinderReentryScreen.lean](KnownCylinderReentryScreen.lean). Episodes14–16 have only script-level residue checks.
