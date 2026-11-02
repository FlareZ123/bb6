# Exact first-passage law and a positive-measure nowhere-dense survival set

Agent 9, 2026-11-02. **Intermediate mathematical analysis of a previously published accelerator; not a BB(6) decision or a new bound.** The original blank-start roots at \(q=141,c=3\) and \(q=17,c=3\) remain undecided. This analysis is for *varying synthetic S-section initial counters* and their compatible 3-adic symbolic extension, not an assertion about either specific integer root.

## Source and convention

Upstream formal acceleration: [Google DeepMind Cryptids, S-root](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean). Existing local [digital coding](./DigitalAperiodic.md) establishes exact residue-word cylinders and a transfer witness in every finite cylinder.

For an integer \(q\ge16\), let \(r=q\bmod3\) and \(k=\lfloor q/3\rfloor\). As long as the S-section survives, the transition is

| r | next q | height change |
|---|---|---|
| 0 | 4k | -1 if c>0, otherwise transfer to T |
| 1 | 4k-3 | +4 |
| 2 | 4k+1 | +6 |

The first visit to a zero-residue step at \(c=0\) is a **transfer to T**, and is **not a primitive Turing-machine halt**. Every surviving step from \(q\ge16\) strictly increases q; hence the table remains applicable at all finite times before transfer.

For fixed length n, reducing the starting q modulo \(3^n\) is in bijection with all ternary digit words \(r_1\ldots r_n\): for a chosen first residue r, write q=3k+r, and the next q equals \(4k+\delta_r\). The multiplier 4 is a unit modulo every power of 3, so the word coding follows by induction. Finite-prefix uniformity is exact, with each word represented by a single class modulo \(3^n\).

## The exact finite-time theorem

Fix initial height \(h\ge0\), and let \(A_{n,h}\) count the residue words of length n for which **the first S-to-T transfer occurs on step n**. Put \(k=h+1\). Then

\[
\boxed{ A_{n,h} = \frac{k}{n}
  \sum_{\substack{a,b\ge0\\5a+7b=n-k}}
  \frac{n!}{a!\,b!\,(n-a-b)!} }
\qquad(n\ge k),
\]

where the sum is zero when \(n-k\) has no representation \(5a+7b\), and \(A_{n,h}=0\) for n<k. Every summand implicitly has a+b≤n; this holds automatically whenever n≥k. The fraction evaluates to a nonnegative integer. The exact probability of first transfer at time n when the initial q-cylinder is chosen uniformly modulo \(3^n\) is \(A_{n,h}/3^n\).

**Proof.** Encode an S step by a queue displacement \(X\in\{-1,4,6\}\), with one of each symbol per ternary digit. The queue initially has k=h+1 items and transfers exactly on its first visit to zero, so \(k+\sum_{i=1}^j X_i>0\) for every j<n and \(k+\sum_{i=1}^n X_i=0\). If a steps are +4 and b steps are +6, summing gives \(5a+7b=n-k\). The number of unrestricted labelled words having those multiplicities is the multinomial factor.

Set \(Y_i=-X_i\in\{1,-4,-6\}\), so \(Y_i\le1\) and \(\sum_iY_i=k>0\). Reversing the word turns the first-visit condition into the requirement that every nonempty partial sum of the reversed Y-word is strictly positive. The generalized cycle lemma for integer increments bounded above by 1 states that exactly k of the n indexed cyclic rotations of any such length-n word with total sum k satisfy this strictly-positive-prefix condition. Count indexed (word,rotation) pairs in two orders: the proportion of first-visit words among all words with these multiplicities is therefore k/n. This proves the formula, including repeated or periodic words because indexed rotations are counted with multiplicity. \(\square\)

Equivalently, interpret the walk as depth-first exploration of a Galton–Watson forest with k initial roots and offspring count 0, 5, or 7 (equiprobable). A transfer is the event that the exploration finishes. For the **finite total-node** probability generating function F(z), elementary root decomposition gives the unique formal series with zero constant term satisfying

\[
F(z)=\frac z3\left(1+F(z)^5+F(z)^7\right),
\qquad
\sum_{n\ge k}\frac{A_{n,h}}{3^n}z^n=F(z)^k.
\]

The coefficient formula follows independently from Lagrange inversion. The cycle-lemma derivation above avoids assuming any probabilistic limit theorem.

## Exact probability of eventual section transfer

Let \(\rho\) be the **unique root in (0,1)** of

\[
1+\rho^5+\rho^7=3\rho.
\]

This is the smaller of the two roots of that equation in [0,1], the other being 1. The probability of *ever* transferring from S with initial height h, under uniform 3-adic digit input, is **exactly** \(\rho^{h+1}\).

**Proof.** The probability that a one-root offspring tree becomes extinct by generation d obeys \(e_0=0\) and
\(e_{d+1}=(1+e_d^5+e_d^7)/3\). Hence \(e_d\) increases and converges to the smallest fixed point of this polynomial map. The polynomial \(g(x)=1+x^5+x^7-3x\) is positive at 0, zero at 1, and has \(g''(x)=20x^3+42x^5>0\) on (0,1). Its derivative is negative at 0 and positive at 1. Consequently it has exactly one additional root \(\rho\in(0,1)\). By monotonicity, \(e_d\le\rho\), and its limit is a fixed point; it is therefore \(\rho\). A forest of k independent root trees becomes extinct with probability \(\rho^k\). The depth-first queue interpretation identifies extinction with finite-time S transfer. \(\square\)

For either known height-three root, \(k=4\). Exact rational sign evaluations at the endpoints certify

\[
\frac{334894995}{10^9}<\rho<\frac{334894996}{10^9},
\quad
0.0125786672384<\rho^4<0.0125786673887.
\]

The complement's 3-adic probability is therefore above 0.9874213326113. This is a statement about randomized *synthetic* starting counters, **not a probability that the particular q=17 or q=141 Turing machine will not halt**. Conditional on any given finite nontransferring digit prefix ending at height h, the future-transfer probability is exactly \(\rho^{h+1}\).


## Uniform exponentially decaying finite-transfer tail

The exact cycle-lemma count gives an immediate **all-horizon bound with an extra 1/n prefactor**, sharper than the earlier pure exponential tilt bound. For any real \(t>0\) such that \(\alpha(t)=(1+t^5+t^7)/(3t)<1\), and all \(n\ge k=h+1\):

\[
\frac{A_{n,h}}{3^n}\le \frac{k}{n} t^k\alpha(t)^n.
\]

Indeed, if \(B\) is the unrestricted multinomial count of words with \(5a+7b=n-k\), the nonnegative-coefficient polynomial \((1+t^5+t^7)^n\) contains \(B t^{n-k}\) among its terms. Thus \(B t^{n-k}\le(1+t^5+t^7)^n\), and the exact first-passage factor k/n yields the inequality. Consequently, for any \(N\ge k-1\),

\[
\Pr(N<\tau<\infty)\le\frac{k\,t^k\alpha(t)^{N+1}}{(N+1)(1-\alpha(t))}.
\]

Taking \(t=15/22\) gives the exact rational \(\alpha=3032754763/5102095680<1\); at h=3 the bound for transfer *after* step 100 is under \(3.216\times 10^{-25}\) in the uniform 3-adic symbolic model. This is an explicit **unconditional tail over randomized starting counters**, and says nothing deterministic about q17 or q141. The exponent is near-optimal within polynomial tilting: \(\alpha(t)\) attains its minimum at the unique positive \(t_*\) solving \(4t_*^5+6t_*^7=1\); approximately \(t_*=0.681773663149\), \(\alpha(t_*)=0.594413535584\). The derivation uses only finite multinomial expansion and a geometric series, with no numerical asymptotic assumption. Relative to the existing [GenericTail](./TailMass.md) rational tilt, the exact first-passage formula supplies the further k/n factor.

## Topological consequence: a fat 3-adic survival set

For fixed initial height h, the set E of 3-adic starting counters with a finite-time S transfer is a union of finite congruence cylinders, hence open. By the existing explicit dense-transfer cylinder construction (see [DigitalAperiodic](./DigitalAperiodic.md)), **E is dense**. Its complement N, the set of section inputs whose digit streams never transfer, is closed and nowhere dense. The new exact probability gives

\[
\mu(N)=1-\rho^{h+1}>0.
\]

Thus N has **positive 3-adic Haar measure while having empty interior**. In every cylinder corresponding to a surviving finite prefix, its conditional measure is \(1-\rho^{h'+1}>0\), where h' is the ending height. The first-exit cylinders and the nontransfer set are simultaneously ubiquitous in distinct measure/topology senses. This makes a finite congruence-only nontransfer certificate for a particular integer root impossible, while leaving open a more elaborate unbounded-arithmetic invariant.

No positive *integer* counter is proved to lie in N. The original BB(6) machine roots, any raw halting behavior after T transfer, and the global BB(6) maximality problem are unaffected.

## Reproduction and evidence level

Run [first_passage_verify.py](./first_passage_verify.py) with standard Python 3. It independently compares the cycle-lemma formula against height-dynamic-program counts for h=0,1,3,8 through n=160 and brute-force ternary enumeration through n=9. It also checks the q-residue/digit-word bijection through n=7 and evaluates the rational root bracket *exactly* with Fraction. These checks are finite falsification tests; the general theorem rests on the mathematical cycle-lemma and branching-process proofs above. **The general counting formula and extinction law are proved mathematically here but have not been fully Lean kernel checked.** The companion [FirstPassageArithmetic.lean](./FirstPassageArithmetic.lean) compiled locally in Lean 4.36.0-rc2: it kernel-verifies the universal first-passage length identity and the exact integer polynomial signs defining the stated rational root bracket. Its printed axioms are [propext, Quot.sound] for the length identity and [] for both integer signs, with no sorryAx. Its source SHA-256 is `97c0c8f9a8f6248d2fb4fc45cb2a89ecbe2d8b18fb7f849cde456f624b7083d9`. This is a new exact characterization within our local work, subject to external prior-art review and formal proof integration. Promote neither the theorem nor the probabilistic inference to a resolved-root or solved-BB(6) claim.
