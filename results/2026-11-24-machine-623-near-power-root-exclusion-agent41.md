# Machine #623: source-certified infinite root exclusions and compressed inverse certificates

## Scope and main theorems

The literal six-state machine is `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`. Its authenticated blank macro-orbit starts at D(0,7). All authenticated returns have even first counter. The family

    H_p = D((3^p-5)/2, (13*3^p-4p+7)/2), p >= 8 even,

consists of synthetic three-return halters (see the existing [Agent22 source theorem](../im-results/agent22-623-robust-band/Agent22ThreeStepSource.lean) and [complete dossier](../im-results/agent41-623-fatal-preimages/README.md)). It is not asserted to exhaust the machine's halting states.

**Theorem 1 (kernel-accepted on pinned source).** For every r>=1, H_(6*3^r) is excluded from every authenticated blank-origin return index. The quantification over r and the return index is unrestricted.

**Theorem 2 (kernel-accepted on pinned source).** A finite compressed inverse certificate accepted by `check` proves exclusion from every authenticated blank-origin return index of the represented near-power state. It covers all possible even-first predecessors, not merely sampled candidate parents. In particular, H_5288 is excluded by a 34-node certificate of depth 23.

The original source CI [45408251011](https://github.com/FlareZ123/bb6/actions/runs/45408251011) compiled `power_three_root_excluded`, `check_excludes`, `checked5288` and `excluded5288` with only propext, Classical.choice and Quot.sound (the pure finite certificate needs fewer). It later stopped at a separate symbolic extension's Lean 4.35 decision-instance inference, which does not undo the accepted preceding source theorems. The original-machine source is pinned to Cryptids c86f15861709b76042998c5211c7b2f83991621b.

## Mathematical mechanism

Let N1,N2 count ordinary ternary digits 1,2, and P,M count balanced ternary digits +1,-1. Every reachable H_p forces one of two strictly increasing inverse-index equations:

    p  = 3t - 1 - 2N1(t) - N2(t)
    3p = 3t + P(t) + 2M(t) + 1.

For p=6*3^r, the first index jumps from p-1 to p+3 at adjacent arguments 2*3^r+1 and 2*3^r+2. The second jumps from 3p-3 to 3p+1 at adjacent arguments p-3 and p-2. Both equations are therefore impossible. The source envelope, root parity and blank start complete Theorem 1.

For a general near-power target, represent the counters by (C*3^k+u)/2 and (D*3^k+v)/2. A positive-budget block b=(D*3^h+w)/2 has residue r=2w mod 3 and the exact next residual (w+4r-6)/3. Its drift and excess charges depend only on r. The signed residual contracts outside [-3,3], with fixed points -3,-1,1 and a two-cycle -2,0. Arbitrarily long tails can be evaluated exactly using linear charges. A strict bracket between consecutive allowed blocks in a parity sector excludes the whole sector; equality reconstructs its unique parent. Recursive certificates close all possible parent sectors or reject. Theorem 2 uses induction on the certificate tree and the original-source exhaustive inverse envelope.

## Density and further exact algebra

The [dossier](../im-results/agent41-623-fatal-preimages/README.md) includes a paper proof that each individual gate occurs for X/6+o(X) even exponents up to X. Therefore at least one third of even exponents are excluded already by missing both gates (lower asymptotic density). The explicit six-character Fourier inversion in the dossier sharpens these counts to X/6+O(log X) and X/6+O(X^(log_3 2)), respectively, hence at least X/6-O(X^(log_3 2)) missing both gates. This density argument is mathematical, not yet an end-to-end Lean asymptotic theorem.

The pure [shared digit decoder](../im-results/agent41-623-fatal-preimages/FatalFamilyDigitDecoder.lean) has locally kernel-accepted soundness and completeness in Lean 4.36.0-rc2. For tau=(3^m-1)/2, balanced weight is 2m minus ordinary weight at t+tau. Both index equations can use the same most-significant-digit decoder, with disjoint high-digit intervals, and only O(log p) digit steps. The source bridge and a pure finite googol-exponent missing-gate certificate are present in the dossier but await separate pinned-source acceptance.

## Symbolic extensions and remaining proof obligation

The pure symbolic checker uses affine forms a*9^n+b*n+c and nested stable-tail pumping. It has locally kernel-accepted arithmetic soundness and 133 complete symbolic certificate equalities (370 tree nodes) for p=6*3^(R+2n)+c, R=30,31 and selected even c in [-100,100]. A further exact Python search found 1,355 candidate infinite families across ten normalized leading coefficients. The actual original-source transfer of these symbolic certificates is being validated; this note does not elevate local interface-stub compilation to source acceptance. See [symbolic certificate dossier](../im-results/agent41-623-fatal-preimages/README.md) and the reproducible generator.

The main open quantifier remains: exclude **every** possible halt from the authentic #623 blank orbit, or exhibit an authentic halting trajectory. The present results do not decide #623 or establish BB(6) maximality.
