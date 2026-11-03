# Agent 46: pinned primary Rocq source for five October BB(6) reported halters

**R006 independent original-source review, 2026-11-03. Intermediate provenance, not a new BB(6) solution.** The original proofs were produced externally by mxdys/the BusyCoq collaborators, not discovered here. This audit located their public primary Rocq source and established the exact rooted transition-table correspondences. It does not claim independent kernel compilation until the separately recorded compilation run succeeds.

## Primary source and reproducibility

- Original repository: [ccz181078/busycoq, \`BB6\` at 33209bc7dc282b38c8cd6be507bfc551fea56108](https://github.com/ccz181078/busycoq/tree/33209bc7dc282b38c8cd6be507bfc551fea56108/verify).
- Original [\`verify/Others_v3.v\`](https://github.com/ccz181078/busycoq/blob/33209bc7dc282b38c8cd6be507bfc551fea56108/verify/Others_v3.v), Git blob SHA-1 **ab372a2521d386c39ce68e57baa5d6d52d1f49d0**, 21,449 bytes, pinned verbatim as [Others_v3.v](Others_v3.v).
- Original [\`verify/Others_v4.v\`](https://github.com/ccz181078/busycoq/blob/33209bc7dc282b38c8cd6be507bfc551fea56108/verify/Others_v4.v), Git blob SHA-1 **82c3fe38fc4d56d45722e27190745ba7a068ecba**, 41,188 bytes, pinned verbatim as [Others_v4.v](Others_v4.v).
- Original semantic dependencies at same upstream commit: \`verify/TM.v\` (c0 and halts), \`verify/Permute.v\` (all-time state-permutation), \`verify/Flip.v\` (left/right tape reflection and exact-number-of-steps preservation), \`verify/ES_v3.v\` (the computational \`native_check_eq\` tactic), plus other imported BusyCoq modules. These original source dependencies must be included in any claimed full source verification.
- [audit.cjs](audit.cjs) checks the original two Git blob hashes, finds and checks the actual literal tables and halting-existence theorem declarations, proves exact twelve-action direct/mirror matching by string transformation, and independently compares first 10,000 primitive blank-tape steps for each pair (including the tape reflection). The 10,000-step simulations are regression tests of table identity only; they are not halting proofs. **Manual GitHub Actions [41569363220](https://github.com/FlareZ123/bb6/actions/runs/41569363220) SUCCESS**. The check never modifies external files or generates any machine decision.
- Additional [OriginalRootMirror.v](OriginalRootMirror.v) composes original \`TM7.halt\` and \`TM6.halt\` with the original \`Flip BB62\` theorem. It states \`halts\` for the actual reported unreflected blank-A machines; its \`raw_steps_preserved\` lemma preserves every exact primitive step count conditionally. **Until compilation against authentic dependencies succeeds, this source bridge is an unverified candidate**, not a new formal certificate.
- Manual-only [.github/workflows/agent46-rocq-root-audit.yml](../../.github/workflows/agent46-rocq-root-audit.yml) runs the lightweight audit by default. Its optional \`compile_rocq\` mode checks out the exact upstream commit and attempts a transitive-dependency Coq build. A compilation attempt is independent evidence only if **all source, checker, and final bridge steps succeed**.

## Exact five-source correspondence

All entries below use the *blank tape, initial state A*. The October source report is [2026-10-21--26 Discord digest](https://github.com/Yeyito777/bbchallenge-corpus/blob/32869adbaef967d9e43bc97f1ed13c076558a71d/knowledge/discord/bb6/chat/2026-10-21--2026-10-26.md), which attributes these original results to mxdys. The following table is verified from the pinned **primary** source, not from the digest's proof-status assertions.

| Reported original rooted RLE | Original Rocq module and theorem | Match |
| --- | --- | --- |
| \`1RB0LC_1RC0RC_1LD0RB_1LA1LE_0RA0LF_0LD---\` | \`Others_v3.TM9.halt\` | literal |
| \`1RB0LD_1RC1RE_1LD0RA_1LA0LA_0LC0RF_0RB---\` | \`Others_v3.TM6.halt\` | exact L/R reflection |
| **\`1RB1RE_1LC0RD_1LD0LD_1RA0LC_0LB0RF_0RA---\`** (October 16 row 311) | \`Others_v3.TM7.halt\` | **exact L/R reflection** |
| \`1RB0RB_1LC0RA_1LE1LD_0RE0LF_1RA0LB_0LC---\` | \`Others_v3.TM8.halt\` | literal |
| \`1RB1LD_1RC0RB_0LA1RE_1LA0LB_0RA0RF_---0LC\` (October 16 line 584) | \`Others_v4.TM.halt\` | literal |

In the reflected row311 case, original source \`Others_v3.v\`, lines 464–481:
- \`TM7.tm\` is \`1LB1LE_1RC0LD_1RD0RD_1LA0RC_0RB0LF_0LA---\`.
- \`TM7.same_table : Perm tm TM9.tm state_map\` has a twelve-case \`destruct q,b\` proof and explicitly maps its blank initial A to \`TM9\` initial D.
- \`TM7.from_check n\` obtains \`halts TM7.tm c0\` from \`TM9.check n D = true\` using original \`perm_halts'\`.
- \`TM7.halt : halts TM7.tm c0\`, closed by \`apply (from_check 1000000000%N). native_check_eq. Qed.\`
- The published \`Flip.v\` source supplies \`flip_halts_in\` for **every** \`n\`, as well as \`flip_halts\`; replacing every L/R in the reported original gives exactly \`TM7.tm\`. The blank tape is unchanged by reversal.

\`Others_v3.TM9.halt\` is at lines 439–440; \`TM6.halt\` at 460–461; \`TM8.halt\` at 499–500. \`Others_v4.TM.halt\` at lines 889–890 is a separate checker-backed blank-A theorem for the fifth machine.

## Scope, step counts and trust boundaries

The primary \`TM.v\` source defines \`halts tm c0\` existentially, as \`∃ n, halts_in tm c0 n\`, with \`halts_in\` reaching a halted configuration after exactly \`n\` primitive transitions. The \`native_check_eq\` proof is applied to an **accelerated checker** with limits 1,000,000,000 (\`TM9/TM6/TM7/TM8\`) or 20,000,000,000 (\`TM\` in \`Others_v4.v\`), not to raw-machine runtime scores. The external digest reports **15,074,368,710,199** primitive steps for row311 and **28,061,938,903,302** for row584; **these numeric counts are simulation reports**, not established by the source theorem statements. A separate certified raw step witness would be required to promote those precise scores.

The source computational tactic \`native_check_eq\` is defined in \`ES_v3.v\` as \`native_cast_no_check (eq_refl a)\`. Despite the name, the documented tactic directs the Rocq kernel to use native conversion when checking term types (see [official documentation](https://rocq-prover.org/doc/V8.18.0/refman/proof-engine/tactics.html)); it is not an \`Admitted\` instruction. Nevertheless, actual successful compilation and an assumptions check are necessary for an independent verifier's certification claim. Source text alone, a green short Node job, or a simulation check does not substitute for that.

**What this resolves:** first-hand original-proof *location* and precise rooted-table identity for all five of the October-reported cases, including the easily missed exact mirror from the original blank A. Their source \`halts\` claims have explicit raw-semantic proof paths; compilation verification is pending. **What remains:** independently execute the Rocq kernel build, audit any axioms, certify numeric step counts separately if scientifically needed, and solve unclassified roots. No new BB(6) upper bound, lower bound, or exact result follows.
