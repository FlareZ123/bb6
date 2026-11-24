# Cryptids #429: original-source halting gates and inverse obstructions

**Research state (6 November 2026): source-verified necessary halting-gate reductions; the genuine blank-start decision remains open.** The full original argument, residue derivations, experiments and verification chronology remain in [FULL_RESEARCH_LOG.md](FULL_RESEARCH_LOG.md).

## Source and strongest integrated gate

The rooted machine is `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. The pinned [Cryptids source](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) accelerates the authentic blank run into counters `J(u,w)`, with a potential halt when `w+1=2u`.

[SourceRawHalt44.lean](SourceRawHalt44.lean) composes all-time rooted modular exclusions into an original raw-machine halting equivalence restricted to **44 necessary terminal residue classes modulo 1024**. The full source build succeeded in [manual CI 41869801195](https://github.com/FlareZ123/bb6/actions/runs/41869801195). Earlier six-class and finer inverse chains, parity restrictions, rank checkpoint proofs and source links are in the [full log](FULL_RESEARCH_LOG.md). Repeated proofs of one congruence class provide independent verification of the same exclusion.

[No765HalfREADME.md](No765HalfREADME.md) describes a separate four-lift mod-8192 restriction with its own source-integration evidence. Its claims need separate verification before composing them with the 44-class theorem.

## Missing blank-root result

None of the surviving necessary gates has been shown reachable by the authentic blank orbit; there is also no uniform nonreachability proof. The presence of parametric **synthetic** halting states in arbitrary moduli does not establish actual blank ancestry. See the [all-moduli limitation](../agent6-429-coprime-moduli/AllMixedModuliZeroSector.md).

[Q0Mod128SixRows.md](Q0Mod128SixRows.md) records a new provisional inverse-tree reduction: six of the sixteen `u mod 16` sectors of the outstanding `(n mod 32, d mod 16) = (23, 7)` q0 family appear excluded using the existing positive-even-eight root invariant. It is not yet compiled against the full source dependency closure, and ten sectors remain open; do not treat it as an integrated result.

**Next proof:** constrain genuine blank-root feeders into all surviving halting gates, including exceptional inverse parents. Check overlap with earlier #429 certificates before producing another residue claim. No #429 halt/nonhalt decision or BB(6) result follows.

## q0 depth-16 inverse sieve (computational; not source-integrated)

[Q0Depth16InverseSieve.md](Q0Depth16InverseSieve.md) and its [C++ reproducer](Q0Depth16InverseSieve.cpp) enumerate the exact inverse branches for the outstanding q0 family against the already source-certified root invariants from Agents 1, 6, and 39. The depth-16 sieve leaves 31,376 residue classes modulo 2^22 (1,004,032 lifts modulo 2^27), and identifies a correction to the older [Q0ResidueCoverage note](../agent1-429-q0-23-7/Q0ResidueCoverage.md): its u=26 mod-64 row substitutes the k residue for u=58. This remains an intermediate computational filter, not a Lean theorem or reachability result. The surviving inverse paths are synthetic candidates; the next step must distinguish genuine blank-root ancestry rather than blindly increasing the modulus.

## Blank-root reset pump (finite computational segment)

[BB429RootResetPump.md](BB429RootResetPump.md) and its [C++ reproducer](BB429RootResetPump.cpp) verify a 3,128,158-cycle (F^{26}E_{\rm odd}) first-return phase on the actual blank-root orbit: ((0,530028452)) at step 149,997,313 returns by repeated 27-step blocks to ((0,805306356)) at step 234,457,579, with the second coordinate increasing by 88 each cycle. This is an exact finite segment and an algebraic macro identity, not an infinite-run or nonhalting proof; the next phase boundary remains open.

## Nested reset pump after the first phase

[BB429NestedResetPump.md](BB429NestedResetPump.md) and its [C++ reproducer](BB429NestedResetPump.cpp) continue from ((0,805306356)) and verify the exact branch word (F^{27}O_{\rm even}E_{\rm even}(F^{24}E_{\rm even})^{1458887}F^{25}O_{\rm odd}E_{\rm odd}), returning to ((0,939524164)) after 36,472,231 transitions. Combined with the preceding root certificate, this reaches that state at root step 270,929,810. This remains a finite computational segment only.

