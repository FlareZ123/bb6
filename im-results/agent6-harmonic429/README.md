# Cryptids #429: original-source halting gates and inverse obstructions

**Research state (6 November 2026): source-verified necessary halting-gate reductions; the genuine blank-start decision remains open.** The full original argument, residue derivations, experiments and verification chronology remain in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).

## Source and strongest integrated gate

The rooted machine is `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. The pinned [Cryptids source](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) accelerates the authentic blank run into counters `J(u,w)`, with a potential halt when `w+1=2u`.

[SourceRawHalt44.lean](SourceRawHalt44.lean) composes all-time rooted modular exclusions into an original raw-machine halting equivalence restricted to **44 necessary terminal residue classes modulo 1024**. The full source build succeeded in [manual CI 41869801195](https://github.com/FlareZ123/bb6/actions/runs/41869801195). Earlier six-class and finer inverse chains, parity restrictions, rank checkpoint proofs and source links are in the [full log](FULL_RESEARCH_LOG.md). Repeated proofs of one congruence class provide independent verification of the same exclusion.

[No765HalfREADME.md](No765HalfREADME.md) describes a separate four-lift mod-8192 restriction with its own source-integration evidence. Its claims need separate verification before composing them with the 44-class theorem.

## Missing blank-root result

None of the surviving necessary gates has been shown reachable by the authentic blank orbit; there is also no uniform nonreachability proof. The presence of parametric **synthetic** halting states in arbitrary moduli does not establish actual blank ancestry. See the [all-moduli limitation](../agent6-429-coprime-moduli/AllMixedModuliZeroSector.md).

**Next proof:** constrain genuine blank-root feeders into all surviving halting gates, including exceptional inverse parents. Check overlap with earlier #429 certificates before producing another residue claim. No #429 halt/nonhalt decision or BB(6) result follows.
