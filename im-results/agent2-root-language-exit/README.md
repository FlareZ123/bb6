# Cryptid D: first regular-language exits of four blank-derived arithmetic seeds

**Status: Lean-kernel-checked arithmetic-model result, not a new original-source blank-orbit theorem.** Exact BB(6), even the original D machine's eventual halting status, remains unknown. The existing [Agent 37 word-level programme](../agent37-root-language-pilot/README.md) and genuine-root original-source reentries from Agent 35 and Agent 37 predate this computation. The purpose of this dossier is to make the first common, root-directed *unclosed section interface* reproducible, and to identify its immediate source-verified exits.

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

The D-start blank-root chain is original-source verified through the sixteenth exceptional reentry; the episode 17–30 continuation and its connection to Seed31 remain pending the staged manual audit described in the [Agent 37 timing-cocycle dossier](../agent37-d-timing-cocycle/README.md). The successful stage-2a artifact covers episodes 14–15 only. No result below should be read as an authenticated blank-root extension until that upstream 17–30 chain is source-verified.

### Seed31: conditional exact arithmetic first stop

The submitted [BlankThirtiethRejoin.lean](../agent37-d-timing-cocycle/BlankThirtiethRejoin.lean) defines the next pure-unary seed as
`seed31 = L(64*t30+117,0,0)`.
An exact BigInt replay of the DRegular recurrence, using independent 512-step and 256-step 3-adic block sizes, gives:

- `t30 mod 81 = 22`; seed31 has 180,684 bits and `seed31.a mod 81 = 67`.
- The first undefined DRegular successor occurs after **12,267** regular transitions, at `L(a,8,1)` with `a mod 59049 = 39637`, `a mod 81 = 28`, and `t31=(a-10)/9 mod 27 = 2`.
- This is not the conditional q=4 cylinder `L(59049*m+44494,4,1)`. The q=4 local closure remains a valid source theorem, but this computed seed31 does not enter it.

This is an exact arithmetic result for the submitted seed31, not a source-certified original-machine root theorem: its dependency on the unverified episode 17–30 root chain is essential. The detailed replay, downstream arithmetic signatures through exception 38, and exact limitations are in [seed31-38-exact-replay.md](seed31-38-exact-replay.md).

### Candidate original-source continuation after the q=8 first stop

The q=8 E/A exception has an existing source return. The E-first packet has p=16=3*5+1, so [EFirstAPacket.exceptional_EA_packet](../agent2-packet-shift/EFirstAPacket.lean) followed by [AOnePacketBoundarySource.a_p1_boundary](../agent2-packet-shift/AOnePacketBoundarySource.lean) returns to the pure-unary seed `L(64*t31+117,0,0)). The candidate root composition is [BlankThirtyFirstRejoin.lean](BlankThirtyFirstRejoin.lean).

The next arithmetic first stop is after 6,106 regular transitions, at `L(9*t32+4,1,1)`, with `t32 mod 27 = 5`. Agent 25's [E3SourceRejoin.lean](../agent25-cryptid-doublezero/E3SourceRejoin.lean) proves the physical two-far-right-blank ObsEq bridge and the q=1,b=1 branch-A return to `L(64*t32+27,0,0)`; Agent 25 reports this branch compiled with only standard axioms. [BlankThirtySecondRejoin.lean](BlankThirtySecondRejoin.lean) composes that shared bridge with the conditional blank-root prefix. The same module also contains branch-B and branch-E reentries for the other two residues of the q=1,b=1 family; branch-E closes the exception-38 tail13 output to `L(64*t38+49,6,0)` via the explicit one-blank ObsEq transport. The all-residue theorem `q1b1_rejoins_regular` has now compiled successfully in [CI run 43420030637](https://github.com/FlareZ123/bb6/actions/runs/43420030637), with only `[propext, Quot.sound]` in its kernel audit. This closes the q=1,b=1 E-section family at source level, but does not certify the blank-root prefix to any of these candidate sections.

The exact first-stop signature, unconditional first-stop corollary, t30 residue theorem, and two blank-root reentry modules have been submitted in Lean. They are **not yet kernel-verified**. The artifact-reusing manual workflow [.github/workflows/agent2-seed31-first-stop-certificate.yml](../../.github/workflows/agent2-seed31-first-stop-certificate.yml) now compiles the certificate, q=8 reentry, Agent 25's q=1 bridge, and q=1 reentry in dependency order. It requires the completed `d-root-seed31-audit` artifact's `source_run_id`; keep the source revision pinned to `2da159d86fa86d813bdfbc54e38e3ec9c75b6e69`. It is manual and does not run on every commit.

### Next discriminating work

1. Complete the original-source episode 17–30 audit and produce the pinned `d-root-seed31-audit` artifact. The existing reusable workflow now has durable manual stages `2b16` (sixteenth reentry checkpoint) and `2b17` (seventeenth continuation plus E7 escape); resume from `d-root-stage2a` through those checkpoints rather than rerunning the combined legacy `2b`. Without the full 17–30 audit, the Seed31 arithmetic is not connected to the authentic blank root.
2. Run the updated certificate workflow. First settle the exact t30 residue and 12,267-step q=8 first-stop theorem; then compile the q=8 E/A source return and q=1 physical two-blank bridge.
3. If those checks pass, source-certify the exception 33 q=5 E/E/A return and the subsequent q=6/q=9 E/B and q=7 E/A returns. For exception 38, reuse Agent 25's compiled `q1b1_regular_rejoin_E` branch, which already proves the one-trailing-blank ObsEq transport for `oppairs(6) ++ [false]`; the remaining task is composing that return with the source-certified root prefix.
4. Continue toward an inductive physical blank-root invariant or find the first genuinely reachable uncovered successor. A finite sequence of prepared-section reentries is not an all-time nonhalting decision.

The previous q=4 instructions remain relevant only for a root path that actually reaches `L(59049*m+44494,4,1)`; they must not be imposed on the q=8 Seed31 branch computed here. No conclusion about the D machine's eventual behavior, BB(6), or the exact Busy Beaver value follows from this intermediate work.
