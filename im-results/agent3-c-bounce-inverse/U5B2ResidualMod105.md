# U5 B2 fan: residual mod-105 restriction on the q≥3 parents

**Status:** exact arithmetic derived from the U5 residual identity and Agent 4's B2 parent parameterization; not yet Lean-compiled and not a reachability exclusion.

Assume the authentic residual identity
\[211t+1360+22155w=20\cdot2^{201+3360w}\]
and the B2 cylinder parameterization
\[h=8+128u.\]
The mod-3/5/7 calculation in `U5Q0ResidualMod105.md` gives \(h\equiv84\pmod{105}\). Therefore
\[8+128u\equiv84\pmod{105},\qquad 23u\equiv76\pmod{105}.\]
Since \(23^{-1}\equiv32\pmod{105}\),
\[\boxed{u\equiv17\pmod{105}.}\]

Agent 4's q≥3 fan uses
\[W=1113+16555u=4^{q-2}(a+3),\qquad Q=\frac{W}{2^{2q-3}}=\frac{a+3}{2},\]
with parent state
\[(a,k)=(2Q-3,\;35246+524288u-Q-3q).\]
Substituting \(u\equiv17\pmod{105}\) gives
\[W\equiv1113+16555\cdot17\equiv98\pmod{105}.\]
Thus
\[Q\equiv98\,(2^{2q-3})^{-1}\pmod{105}.\]
Because the order of 2 modulo 105 is 12, the residue depends only on q mod 6:

| q mod 6 | Q mod 105 |
|---:|---:|
| 0 | 49 |
| 1 | 91 |
| 2 | 49 |
| 3 | 91 |
| 4 | 49 |
| 5 | 91 |

In particular,
\[\boxed{7\mid Q,\qquad a=2Q-3\equiv4\pmod7.}\]
More precisely,
\[a\equiv95\pmod{210}\quad(q\text{ even}),\qquad a\equiv179\pmod{210}\quad(q\text{ odd}).\]
Also, reducing the k formula modulo 105 gives
\[k\equiv42-Q-3q\pmod{105},\]
so
\[k\equiv98-3q\pmod{105}\quad(q\text{ even}),\qquad k\equiv56-3q\pmod{105}\quad(q\text{ odd}).\]

This is a uniform arithmetic restriction on every q≥3 B2 parent. It does **not** establish that any such parent is unreachable. The potentially useful next step is to combine \(a\equiv4\pmod7\), \(7\mid(a+3)\), and the corresponding k residues with the exact source-parent grammar for the parent state itself, rather than treating q as an unconstrained parameter.

## Second-level source-grammar pruning for the B2 parent itself

The same congruences also determine the parent coordinates modulo 3. Since \(u\equiv17\pmod{105}\),
\[W=1113+16555u\equiv2\pmod3.\]
Because \(2q-3\) is odd, \(2^{2q-3}\equiv2\pmod3\), so \(Q\equiv1\pmod3\). Consequently
\[a=2Q-3\equiv2\pmod3,\qquad k=35246+524288u-Q-3q\equiv2\pmod3.\]
The parent is therefore an odd/odd target with \(a+k\equiv1\pmod3\) and \(a+k+1\equiv2\pmod3\).

Consider an incoming source edge to this parent \((a,k)\):
- In the \(a'=0\) branch, the target equation is \(a+k=8\cdot2^n\), while the cost equation is \(2K+9+3n=a+2k\). Since \(a\) is odd, the right side is odd, so parity forces \(n\) even. The target sum is 1 mod 3, but \(8\cdot2^n\equiv2\pmod3\), contradiction.
- In the \(a'=1\) branch, the target equation is \(a+k+1=16\cdot2^n\), with cost \(2K+11+3n=a+2k\). Again parity forces \(n\) even. The left side is 2 mod 3, but \(16\cdot2^n\equiv1\pmod3\), contradiction.

The small exceptional outputs of the \(a'=0\) and \(a'=1\) cases have first coordinate at most 5, whereas the B2 parent has \(a\equiv95\pmod{210}\) for even q and \(a\equiv179\pmod{210}\) for odd q, so those are excluded too. Also \(k\ge5\): from q≥3, \(Q\le W/8\), and \(2^{2q-3}\ge q\) gives q≤W; since u≥17, \(W=1113+16555u\le18000u\), whence
\[k\ge35246+524288u-W/8-3W\ge35246+468038u>5.\]
This excludes the \(a'>1,k'=0\) output with right coordinate 2 and the \(a'=1,k'\ge4,y=3\) exceptional branch. Thus the B2 q≥3 parent itself also has no incoming \(a'=0\) or \(a'=1\) source edge; any possible predecessor must be a direct or nonexceptional bounce parent.

This remains a necessary source-grammar reduction, not a proof that the B2 parent is unreachable.