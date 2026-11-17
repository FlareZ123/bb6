# Lean formalization of the D0-zero t=0 root-exclusion family

Status: the arithmetic module compiles locally with Lean 4.36.0-rc2. The source-connected wrapper is prepared and included in the existing manual-only source workflow; exact-source CI is pending. Do not report the source theorem as CI-verified until that workflow succeeds.

## Result

For every integer n >= 1, define

- a_n = 18n + 2,
- K_n = 3 * 2^(18n) + 8,
- r_n = K_n + 1 - a_n,
- p_n = 2^K_n.

The Lean arithmetic theorem constructs B, D, and E satisfying

- B = (2K + 7) * 2^(r+3),
- 24p <= B <= 28p,
- 3D + 16p = B + 2K + 1,
- E + D = 8p + K,
- 4p <= E + K + 4 and E + K + 5 < 8p,
- r is odd,
- 16p + 4K + 20 <= B <= 28p + 4K + 8,
- 3E + B = 40p + K - 1.

These are the first-entry guards, the t=0 source-band constraints, and the adjacent-fatal identity used in the existing D0-zero phase derivation. The same theorem proves that E has no ResetParent predecessor. The source wrapper then uses the exact source theorem root_reset_chain_iff to conclude that (E,0) is not reachable from the blank reset root (2,0).

The levels K_n are unbounded (hence infinitely many distinct levels). The first member is n=1, a=20, K=786440, r=786421.

## Why no inverse parent exists

The residue data are forced by K = 2 (mod 18), a = 2 (mod 18), and r+a=K+1:

- 2^K = 4 (mod 9),
- 2^(r+3) = 7 (mod 9),
- 2K+7 = 2 (mod 9),
- therefore B = 5 (mod 9).

From 3D + 16p = B + 2K + 1 it follows that D = 0 (mod 3). Also 16p + 2K + 5 = 1 (mod 3), and
2E + 5 + 2D = 16p + 2K + 5,
so 2E+5 = 1 (mod 3). Every odd ResetParent arm requires 3 | (2E+5), a contradiction.

For an even parent at level k:

- if k < K, its output band gives E <= 8*2^k - 3 <= 4p - 3;
- if k >= K, its output band gives E >= 6*2^k - 1 >= 6p - 1.

But the arithmetic gives 4p < E < 6p - 1. Thus no even parent exists either.

The exact source wrapper identifies the copied arithmetic relation with CascadeResetInverse.ResetParent and applies CascadeResetInverse.root_reset_chain_iff. The parentless state E is not the root itself because E > 2.

## Evidence boundary

- T0D0ZeroPhaseArithmetic.lean imports only Std and is kernel-checked locally.
- T0D0ZeroPhaseSource.lean imports the repository's exact ResetChain module. Its local syntax check used a minimal signature stub, not the repository source.
- .github/workflows/agent10-746-exit-source.yml now compiles the arithmetic module and then the source wrapper after the original source dependency chain. The first exact-source CI result is still required.
- This excludes one infinite residue family of t=0 first-entry candidates. It does not resolve all t=0 candidates, all #746, or BB(6).

Underlying derivation: ../agent10-cascade/T0-D0-ZERO-PHASE-ROOT-EXCLUSION.md.
