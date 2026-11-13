# Seed31–38: exact DRegular replay and the actual first exception

**Status:** intermediate computational result; not a Lean-certified root theorem. This note corrects the conditional q=4 first-stop hypothesis for the submitted seed31 definition. Important dependency: the repository's D-root dossier still labels the episode 17–30 original-source continuation as pending CI, so the computed seed31 and every downstream result here remain conditional on that submitted root-rejoin chain. This does not establish BB(6) or an authenticated original-machine blank-root extension.\n\nIndependent source-family result: Agent 25's all-residue q=1,b=1 E-section theorem `q1b1_rejoins_regular` compiled in [CI run 43420030637](https://github.com/FlareZ123/bb6/actions/runs/43420030637), with only `[propext, Quot.sound]`. It covers the branch-A exception32 and branch-E exception38 returns (and the middle branch), but does not authenticate the upstream blank-root prefix.

## Seed31 is not the q=4 cylinder

Using the submitted BlankThirtiethRejoin.seed31 definition
seed31 = L(64*t30 + 117, 0, 0),
I reconstructed the DRegular arithmetic through episode 30 with exact JavaScript BigInt arithmetic. The computed higher residue is:

- t30 mod 81 = 22 (the existing Lean certificate only records t30 mod 27 = 22);
- seed31.a has 180,684 bits and seed31.a mod 81 = 67.

I then searched for the first undefined DRegular successor using the 3-adic shift identity. A 512-step block implementation and a separately parameterized 256-step block implementation agree exactly:

| Field | First stop from seed31 |
|---|---:|
| DRegular transitions | 12,267 |
| a mod 59049 | 39,637 |
| a mod 81 | 28 |
| q | 8 |
| b | 1 |
| successor undefined | yes |

Thus the first exceptional state is L(a,8,1) with a mod 59049 = 39637, not the proposed q=4 state L(59049*m+44494,4,1). Its parameter t31=(a-10)/9 satisfies t31 mod 27 = 2.

The 512/256 implementations both use the exact DRegular recurrence, reducing a modulo 3^B, running the base state for B steps, and lifting by 8^B * floor((a-2)/3^B). This is an arithmetic replay of the same shift law used by DRegularFast; it is not an independent raw-tape simulation.

## Source-return continuation candidates

The following are the subsequent first-stop signatures obtained by iterating the existing submitted source-return formulas. The transition counts and residues are exact in the DRegular arithmetic model. The source compositions listed below still need a single staged Lean audit and, where noted, an explicit padding bridge.

| Exception | DRegular transitions | a mod 59049 | q,b | t mod 27 | t mod 81 | Candidate source continuation |
|---:|---:|---:|---:|---:|---:|---|
| 31 | 12,267 | 39,637 | 8,1 | 2 | 29 | E/A q=8 packet p=16; A-one boundary returns to L(64t+117,0,0) |
| 32 | 6,106 | 58,126 | 1,1 | 5 | 59 | Agent25 q1,b1 branch-A source bridge; returns to L(64t+27,0,0) |
| 33 | 9,276 | 49,579 | 5,1 | 0 | 0 | EAllDouble q=4, E-three, then generic A-code word [false,false,true,true,false,true,true]; proposed pure-unary return L(512u+129,0,0), u=t/3 |
| 34 | 12,638 | 55,039 | 6,1 | 13 | 40 | E/B general return to L(64t+29,1,5) |
| 35 | 335 | 54,265 | 9,1 | 8 | 35 | E/B general return to L(64t+35,1,5) |
| 36 | 615 | 27,469 | 7,1 | 0 | 54 | E/A all-reentry packet closure; returns to L(64t+91,3,2) |
| 37 | 2,348 | 50,584 | 6,1 | 4 | 31 | E/B general return to L(64t+29,1,5) |
| 38 | 1,341 | 24,670 | 1,1 | 13 | 67 | Agent25 q1,b1 branch-E source bridge; returns to L(64t+49,6,0) with explicit one-blank ObsEq |

The q=8 first return at exception 31 is covered by the already-existing EFirstAPacket.exceptional_EA_packet and AOnePacketBoundarySource.a_p1_boundary: the E packet has p=16=3*5+1, so the candidate reentry is the same pure-unary form L(64*t31+117,0,0) used at exception 30.

For exception 33, the proposed composition is explicit: with t=3u and q=5, EAllDouble(q-1=4) produces a suffix 1^10 0 1^6; splitting it as 111 ++ 1^7 0 1^6 feeds the E-three source theorem. Its output tail packetThree ++ 1^7 0 1^6 is false :: wordCode([false,false,true,true,false,true,true]). The A-code theorem then gives the stated unary endpoint. This composition is a proof target, not yet a kernel-checked theorem.

**Prefix-alignment caveat (Agent 25, 2026-11-13):** matching the displayed EAllDouble(q=4) output for `k=3t` to `CryptidThree.full_E_three` forces the E-three parameter `s=8t+1` and hence its output prefix `1^(8s+9)=1^(64t+17)`. Since `t=3u`, this prefix length is `192u+17 ≡ 2 (mod 3)`. The current A-code entries (`Agent35.full_A_code`, `Agent35.full_A_code_double`, `Agent36.full_A_code_E_triple`, and `ACodeFirstReturn.full_A_mixed_code_first_return`) all enter through `init(1^(3k+1) ...)`; `init` adds two leading ones, so their physical prefix is `3k+3 ≡ 0 (mod 3)`. Thus the displayed tail identity alone does not establish the direct E-three-to-A-code handoff. An additional source-certified boundary shift or a different A-return theorem is needed before asserting the proposed `L(512u+129,0,0)` endpoint. This is a signature mismatch in the proposed direct composition, not a proof that no alternative continuation exists.

At exception 38, EZeroZTwoFollow returns init(xs ++ [false]), where xs = 1^(64*t38+47) ++ oppairs(6); the canonical DRegularSource.sourceSection L(64*t38+49,6,0) is init(xs). Agent 25's q1,b1 branch-E theorem, q1b1_regular_rejoin_E, packages this exact source_init_pad 0 1 xs transport and cfgEq_symm reversal with the EZeroZTwoFollow return. The all-residue theorem q1b1_rejoins_regular now compiles successfully in Lean 4.36.0-rc2 (CI run 43420030637), with only [propext, Quot.sound] for input_obs_eq, A/B/E returns, and the wrapper. Since k=(a-4)/3=3*t38+2, branch E is the applicable case for exception38. This closes the entire q=1,b=1 E-section family at source level; the final blank-root composition still depends on source-certifying the preceding episodes.

## Next decisive work

1. A candidate Lean exact first-stop theorem has now been appended to Seed31FirstStopCertificate.lean: it uses decide to certify 12,267 steps, a mod 59049 = 39637, q=8, b=1, then discharges the first-stop bound. It remains uncompiled pending the existing certificate workflow.
2. Compose exception 31 with EFirstAPacket + AOne boundary and lift the result through BlankThirtiethRejoin.blank_thirtieth_reentry.
3. Assemble and audit the exception 32–37 source returns. For exception 38, reuse Agent 25's already kernel-checked `q1b1_rejoin_E` / `q1b1_rejoins_regular`; the remaining task is the preceding blank-root prefix, not the tail-padding transport.
4. Update the conditional q=4/#41 lookahead: it is not the actual first-stop branch for this computed seed31.

Relevant existing files: im-results/agent37-d-timing-cocycle/BlankThirtiethRejoin.lean, Seed31Probe.lean, im-results/agent2-root-language-exit/Seed31FirstStopCertificate.lean, im-results/agent2-packet-shift/EFirstAPacket.lean, AOnePacketBoundarySource.lean, im-results/agent36-cryptid-trace/EZeroZTwoFollow.lean, and im-results/agent37-d-timing-cocycle/ExceptionalEPacketClosure.lean.

A candidate kernel proof of t30 mod 81 = 22 (by decide) has also been added to Seed31FirstStopCertificate.lean. The exact 12,267-step signature, its first-stop soundness corollary, and the t31 source-shape theorem were added there as candidate kernel proofs. BlankThirtyFirstRejoin.lean now composes that certificate with the existing E/A q=8 packet and A-one boundary to return the blank root to seed32 = L(64*t31+117,0,0). The existing agent2-seed31-first-stop-certificate workflow was updated to compile this reentry module after the certificate. These additions are pending the workflow's kernel check; do not describe them as verified until that run succeeds.

A second candidate blank-root composition has been added in BlankThirtySecondRejoin.lean. It takes the pure-unary seed32 through the 6,106-step q=1,b=1 exception, then reuses Agent25E3SourceBridge.q1b1_regular_rejoin, whose two-blank ObsEq transport composes Agent36EZeroZTwoA.a_two_return_multiple_three and returns to seed33=L(64*t32+27,0,0). The certificate workflow now compiles Agent25's E3SourceRejoin.lean before this module. This is still pending kernel CI.
