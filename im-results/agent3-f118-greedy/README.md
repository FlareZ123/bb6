# F118: exact reduction to the Erdős–Graham greedy recurrence

**Claim and scope.** The historical F118 holdout `1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC` has a two-counter section recurrence equivalent to a countdown-controlled version of the classical growing-modulus doubling algorithm in the Erdős–Graham Diophantine problem. The complete equality to the copied public arithmetic section map is **locally kernel-checked**; `F118Source.lean` is the original-source import adapter (locally checked against an arithmetic API stub only, until the actual pinned source closure is compiled). The authentic blank root is not decided. The original machine is identified by its exact RLE and [upstream source at 3647718](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.lean), whose public `isHalt_iff_highLevel_acceleration` theorem bridges to the arithmetic section. Historical holdout-family label F118 is not evidence of current exhaustive roster membership.

## Exact quotient

Encode the upstream private state `D(a,d,c)` as `(r,n,z)=(a,d+c+3,c)`, and `K(a,k,c)` as `(a+1,k+c+3,c+1)`. No mode bit is needed. The quotient commutes with every source transition, including every zero case:

* `r=0,z=0`: halt.
* `r=0,z>0`: reset to `(n-z-2,z+3,z)`.
* `r>0,z=0`: rescue to `(r,n+1,1)`.
* `r>0,z>0`: let `b=⌊2z/n⌋∈{0,1}`; next is `(r-b,n+1,2z-bn)`.

Validity is `n≥3,z+2≤n`, strengthened to `z+3≤n` if either `r=0` or `z=0`. The authentic source start maps to `(0,4,1)`. The high-level section starts `(a,c)=(0,1)`; a positive-countdown drain starts `(a,c+3,c)`, stops precisely when the countdown reaches zero, and if the resulting pair is `(N,Z)` returns `(N-Z-2,Z)` unless Z=0 (halt). The drain is total: the lexicographic natural rank `(r,n+1-2z)` with truncated subtraction decreases on every active step. At least one selected bit occurs in finite time, independently of the open question of termination of the zero-absorbing greedy map. The checked theorem `section_eq` proves equality on **all** natural section inputs, including c=0, rather than just a test trace.

The mass of each returning section increases: if t active steps consume exactly a wraps, the new mass is c+t+1 ≥ a+c+1. After the initial section every a is odd because the last wrap gives N-Z-2=2(n-z)-1. These two observations are paper corollaries of the checked recurrence.

## Classical number-theoretic identification

For a positive residual, write its dyadic value as `R=z/2^(n-1)`. The greedy test for whether `n/2^n` fits in R is exactly 2z≥n, and after the test the updated value is `(2z-bn)/2^n`. This is the recurrence of Borwein–Loring (1990), [Some Questions of Erdős and Graham on Numbers of the Form Σg/2^g](https://doi.org/10.2307/2008700), and Tengely–Ulas–Zygadło (2020), [On a Diophantine equation of Erdős and Graham](https://arxiv.org/abs/2008.01501), Section 3 (p. 9 of the preprint). Their Theorem 3.5 verifies the modified greedy representation for 2≤m≤10^4. The general finite-representation problem and the stronger universal greedy-termination conjecture must be distinguished.

A section with c≥1 starts at modulus c+3 with residual c/2^(c+2), which is exactly what remains after forcing the first term (m+1)/2^(m+1) of m/2^m, m=c+1:
```
m/2^m - (m+1)/2^(m+1) = (m-1)/2^(m+1).
```
Consequently the *first* zero in a drain is at the (k(m)-1)-st selected term if the modified greedy expansion terminates with k(m) terms. If a is smaller, the section returns before that zero; if a is larger, a zero is rescued and the algorithm continues with the new dyadic unit 1/2^n and first available index n+1. The F118 section halts **iff its a-th selected term yields zero**, including all intervening rescues. Neither universal greedy termination nor its negation decides this particular machine without controlling the selected-term count at successive returns.

## Exact block accelerator (paper proof)

For a zero-absorbing block of t decisions at current modulus n, assume B=2^t≤n. Represent its t wrap bits as the binary integer W, with b_j its bit at place t-1-j. Define J(W)=Σ_{j=0}^{t-1} j b_j 2^(t-1-j), so 0≤J(W)≤B-t-1. Telescoping gives terminal residual q-F(W), where q=Bz and F(W)=nW+J(W).

F is strictly increasing: an increment with k trailing ones changes F by n+t+1-2^(k+1)>0 (k<t). Greedy selection is the lexicographically maximal affordable bit word, since each chosen prefix can be extended by zero bits; hence W is the largest integer with F(W)≤q. In particular W is either floor(q/n) or one less, because J(W)<n. This computes t decisions by one quotient, a table lookup and one comparison; subtract popcount(W) from the countdown. If the final residual is positive, no intermediate zero occurred, since zero is absorbing in the comparison recurrence. Otherwise fall back to the scalar recurrence to distinguish rescue from halt. A block is used only when the countdown exceeds t, so the section cannot end inside it. This derivation does not require a probabilistic assumption.

`fast.cpp` implements 8- and 16-bit blocks with exact unsigned 128-bit intermediates within its tested 64-bit counter range. It checks the 8-bit blocks exhaustively at moduli 256..1023, a deterministic 100,000-case 16-bit sample and all 9,900 independent copied-source section calls with 0≤a<100, 1≤c<100. The finite authentic-root experiment, not a proof of nonhalting:
```
g++ -std=c++20 -O3 -march=native fast.cpp -o fast
./fast 10000000000
```
At section 49 the input was (2408814429,1483721052), after 7785199383 active residue steps. At the budget cutoff (rounded up by at most 15 steps) the in-progress drain was (r,n,z)=(1301442367,3698521680,2851462672). No halt was found. Active residue steps are not primitive TM steps. Do not use this fixed-width simulator with counters near the integer limits.

## Verification and next mathematical target

`lean F118Greedy.lean` under Lean 4.36.0-rc2 succeeds; all exported axioms are within propext, Classical.choice, Quot.sound. The actual source-import check uses the existing manual shared Cryptids audit with dependency `im-results/agent3-f118-greedy/F118Greedy.lean`, bridge `im-results/agent3-f118-greedy/F118Source.lean`, original module given above, pinned commit 3647718b5df22e1a61462dec0376bd204526285a, Lean and dependencies v4.36.0-rc2. The adapter has only local arithmetic-stub preflight at this checkpoint; no claim of full upstream acceptance is made.

Focus on the all-time selected-term-count condition for the actual (a,c) orbit, especially exact coalescence and the set of zero-event ranks in the nonautonomous doubling map. The literature connection is useful but is not a proof that F118 is equivalent to the full Erdős–Graham conjecture.
