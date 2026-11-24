# Space Needle: four-step cubic gain and exact target cutoff

**Status (24 November 2026):** the universal arithmetic four-edge inequality, finite-prefix induction, executable fuel bound, and original blank-root source wrapper are now kernel-checked. The pinned original-source gate passed [CI run 45328855632](https://github.com/FlareZ123/bb6/actions/runs/45328855632). The audited source-facing theorem profiles are exactly [propext, Classical.choice, Quot.sound]. No Space Needle or BB(6) decision is claimed.

## Main result

For the exact shifted-counter edge of Space Needle,

    b = 2^v(2q+3),  b' = b+v+3(q+1),

every four consecutive successful edges from b to B satisfy

    b^2 ≤ 64*L*(B-b)^3

for L=1+floor(log2 b), or any positive L with b<2^L. This asymptotically improves Agent20's source-certified two-step square-root gain. [NeedleFourStep.lean](NeedleFourStep.lean) proves the all-natural theorem.

## Proof

Let b_i=a_i r_i, a_i=2^v_i, r_i=2q_i+3 and g_i=v_i+3(q_i+1). Write G=B-b, m=min_i v_i and A=2^m. Every r_i≤g_i≤G; choosing a source with a_i=A gives b≤AG. Each g_0,g_1,g_2 is a positive multiple of A because both adjacent source counters are divisible by A.

Assume 64 L G^3<b^2. Then G<b, A^2>64LG, A^3>64Lb, and A>64L because A≤G. Every source is below 2b, so v_i≤L and v_i≥m≥2. Write a_i=A s_i and g_i=A k_i for i=0,1,2. The exact identity 2g_i=2v_i-3+3r_i and A>2L imply A≤3r_i. Consequently A^2 s_i≤3b_i≤6b. Define F_i=(2v_i-3)s_i. Then A^2 F_i≤12Lb, giving 4F_i<A. Also 12k_i<A follows from A k_i≤G and A^2>64LG.

The scaled adjacent-edge relation is

    2 A s_(i+1) k_(i+1) + F_i
      = 2 A s_i k_i + F_(i+1) + 3 k_i.

For i=0,1 both residues are smaller than 2A. Reducing modulo 2A yields F_i=F_(i+1)+3k_i, hence v_i>v_(i+1) by monotonicity of F in v. Cancelling the residues also gives s_i k_i=s_(i+1)k_(i+1). Thus v_0>v_1>v_2 and a_0 g_0=a_1 g_1. Since a_1 divides b_0 and b_1, it divides g_0, so a_0 divides g_1. Therefore 2^(v_2+1) divides b_1+g_1=b_2, contradicting its odd-part factorization.

## Exact target fuel

For target d, put X=d+2 and choose

    L=1+floor(log2 X)
    H=4*2^floor((floor(log2 L)+3)/3)
    R=2^floor((L+2)/3)
    cubeFuel(d)=28*H*R.

Then H^3≥64L and R^3>X. A four-edge block beginning above m^3 gains G with HG≥m^2. Thus 7H blocks gain at least 7m^2≥(m+1)^3-m^3 for m≥1. Starting positive, induction gives (k+1)^3≤b_(28 H k) whenever that prefix exists. A successful prefix of length ≥28HR ending at X would contradict R^3>X.

[NeedleCubicFuel.lean](NeedleCubicFuel.lean) proves the exact natural-number cutoff. The explicit fuel is O((X log X)^(1/3)) high-level transitions, asymptotically improving O(sqrt X). The constants can make the earlier cutoff better for some finite targets. This is not a bit-complexity or primitive-step count.

## Original-source verification

[NeedleCubicSource.lean](NeedleCubicSource.lean) imports Agent20's original-source bridge and scanner, then proves:

- `original_four_step_cube_gain`: the four-edge inequality for the exact original `highLevelNext`;
- `original_iterate_cube_bound`: every successful genuine blank-root visit to target d occurs before `cubeFuel d`;
- `cubeScan_spec`: the executable single-pass test satisfies `cubeScan d = true ↔ ReachN d`.

The existing manual workflow `.github/workflows/agent20-needle-growth.yml` was reused with its `cubic` target. [Run 45328855632](https://github.com/FlareZ123/bb6/actions/runs/45328855632), on repository commit `a5f406ce6eb9d62988a551dfa47d5d454e39e8df`, rebuilt the original machine and dependencies from `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371` under the upstream Lean 4.35.0-rc4 toolchain. The run compiled all three cubic modules against those unchanged source definitions. Its `#print axioms` output for the three source-facing theorems above was exactly [propext, Classical.choice, Quot.sound], with no `sorryAx` or unapproved oracle.

## Remaining work

The unbounded existential over genuine terminal targets d+2=2^K remains open. The theorem decides each supplied target with a stronger finite cutoff; it does not give a uniform bound on K, exclude every terminal event, or prove the authentic orbit infinite. The next useful mathematical step is a root-sensitive restriction on the terminal-feeder history that closes an unbounded family, not another finite target scan. External novelty remains unreviewed.
