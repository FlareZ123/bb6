# Space Needle: all-depth exceptional-cancellation history constraints

**Status:** locally Lean 4.36.0-rc2 kernel-checked arithmetic theorem on the exact compact affine inverse update used by Agent20. It bounds exceptional signed-power cancellations across an entire reverse history, for every terminal exponent. It does not exclude ordinary inverse parents or decide the blank-root terminal existential. Original-source import and external novelty review remain open.

## Result

Start at the shifted terminal counter b=2^K, represented as 2Lb=2^n+d with (n,L,d)=(K+1,1,0). In the [all-depth affine inverse grammar](../agent20-needle-coprime/TerminalAffine.md), a predecessor of valuation v uses m=v+1 and the exact update

    n' = n+m
    L' = L(2^m+3)
    d' = 2^m(d+L(5-2m)).

Let S be the sum of all earlier inverse parameters m, initially zero. At every depth,

    n = K+1+S
    L ≥ 2^S
    -2SL ≤ d < 2L.

If a potential predecessor has m≥4 and is in the exact exceptional cancellation alternative

    n % m = 0
    C = d+L(5-2m) = -(-3)^(n/m),

then it necessarily satisfies

    (5m-8)S < 8(K+1).

This holds across every inverse branch, irrespective of the sizes of the coefficients, and even for the larger class of arithmetic histories that need not satisfy the legal-parent test.

### Consequences

* After 3S≥2(K+1), **no** exceptional cancellation m≥4 can occur.
* Once S>0, the exceptional candidate is bounded by the strict inequality m < (8(K+1)+8S)/(5S). This gives an integer test before the exceptional-candidate search.
* For any M≥4 with (5M-8)M≥8(K+1), at most one cancellation of parameter m≥M can occur on any reverse path. After its first occurrence S≥M and every later such event contradicts the budget. More generally, if there are r such events then (5M-8)(r-1)M < 8(K+1), by applying the budget at the last event.
* The lower correction bound is also new in this dossier: the magnitude of the normalized negative correction cannot exceed 2S. This is useful for an a priori bitlength bound in the ordinary rotation test.

## Proof

The affine update gives n=K+1+S and L≥2^S by induction. For the upper correction inequality use 2^m(5-2m)≤6. For the lower inequality, d≥-2SL implies C≥-2(S+m)L, so 2^m C≥-2(S+m)L(2^m+3). These are preserved under every positive m update.

For m≥4, d<2L gives C<-(2m-7)L≤-L. If C is the exceptional signed power, its absolute value is 3^k for k=n/m. Consequently 2^S≤L<3^k. Raising to the fifth power and using 3^5<2^8 yields 5S<8k. Multiplication by m and n=K+1+S give the advertised budget.

The argument actually permits any positive integer pair (a,b) with 3^a≤2^b in place of (5,8); the Lean file uses the simple strict comparison 243<256.

## Denominator-history obstruction

For a legal exceptional cancellation, let k=n/m>0 and D=2^m+3. The complete divisibility condition is

    LD | (2^m)^k - (-3)^k.

If D already divides L (in particular, if the same inverse parameter appeared earlier, whether ordinarily or exceptionally), then D² divides this difference. Expanding (D-3)^k modulo D² gives k(-3)^(k-1)D. Since gcd(D,3)=1, it follows that D | k. Thus a repeated parameter cannot be an exceptional cancellation whenever 0<k<D. No primality of D is needed.

For every previously used parameter a, its denominator D_a=2^a+3 divides L. The same legal cancellation implies 2^n ≡ (-3)^k mod D_a. Raising to a and using 2^a≡-3 gives

    D_a | (-3)^n - (-3)^(ka).

Since -3 is invertible modulo D_a, the multiplicative order divides k|m-a|. The divisibility identity is kernel-checked; the multiplicative-order interpretation is its elementary mathematical corollary. These conditions use the actual accumulated denominator rather than only the current target size, and are necessary tests, not replacements for the full legal-parent check.

## Verification and integration

[NeedleCancellationWeight.lean](NeedleCancellationWeight.lean) compiled locally using Lean 4.36.0-rc2, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, with only Std imports. The exact local Git blob is 86761effee05dedb8dbf38a9cc1b8ca3da8a3a0c (SHA-256 6b5fd8c7f75130fce0b2a43ec64aabbdad09a9f31906245f2705d29a8a859efe). The seven audited declarations root, step, cancellation_budget, no_late_cancellation, history_weight, no_second_large and history_cancellation_budget depend only on standard Lean axioms [propext, Classical.choice, Quot.sound] or a subset; no sorryAx or native_decide.

[NeedleCancellationRepeat.lean](NeedleCancellationRepeat.lean) likewise compiled locally with only standard axioms. Blob f31a8ee47dde1a2d8a0a39333517682b9790b84d; SHA-256 8f2d1d3516793a147990c67c33aa6e68da3ffe31090afdccb394bca84682c5e1. The audited declarations include the first-order signed binomial identity, denominator coprimality, the square-divisibility obstruction, repeated-parameter exclusion, and cross-parameter divisibility.

The explicit History relation starts from the terminal form and inductively uses the exact same affine update. Its theorem can be composed with Agent20's existing terminalForm_parent and source_terminal_affine_parent once their original-source closure is accepted. This invocation did not import or compile the unchanged external Cryptids source; direct local GitHub resolution failed. No CI was launched.

For terminal_affine_solver.cpp, S=n-(K+1), so no new stored coefficient is needed. Skip the large-exception search after 3S≥2(K+1); otherwise cap its m by the strict budget. Ordinary candidates still require the original complete divisibility and positivity tests. This is a lossless exceptional-sector restriction, not a uniform proof of nonreachability.

## Remaining mathematical obstruction

The ordinary rotation sector survives at arbitrarily large terminal exponents, and this theorem supplies no bound on the root-reaching exponent K. The next useful target is a root-sensitive obstruction in that sector, or a way to exploit the now bounded number of large exceptions to close a full family of reverse histories. No Space Needle decision or BB(6) bound is claimed.
