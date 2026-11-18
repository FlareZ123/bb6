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
