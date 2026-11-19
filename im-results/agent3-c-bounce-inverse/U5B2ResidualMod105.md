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

## Exact parity split of the complete B2 parent grammar

The mod-105 residues above give a further all-depth reduction when combined with the exact source grammar `section_preimage_all_iff`.

For every q≥3, Q is odd (both residues 49 and 91 modulo 105 are odd), so
`a=2Q-3` is odd. The displayed k formula gives
`k ≡ 1+q (mod 2)`: k is odd for even q and even for odd q. The established bound k≥5 also removes all small exceptional outputs and the source case k'=0.

Now let `(a',k')` be any source predecessor of the B2 target `(a,k)`. The exact original-source preimage grammar and the preceding mod-3 contradictions give:

- The source `a'=0` branch is impossible for every q.
- The source `a'=1` branch is impossible for every q.
- The source `k'=0` branch is impossible because it would output right coordinate 2.
- A direct source branch has target right coordinate `k=2*k'+2`, hence is possible only when q is odd.
- An even-`a'` recursive bounce has target sum `a+k=2^n*(2*a'+4)`, hence is possible only when q is even.
- An odd-`a'` recursive bounce has target sum `a+k+1=2^n*(2*a'+6)`, hence is possible only when q is odd.

Therefore the exhaustive source-parent alternatives reduce to the disjoint parity cases:

**Even q:** every possible source predecessor must be an even-`a'` bounce parent (with its original unbounded depth witness).

**Odd q:** every possible source predecessor is either the direct parent or an odd-`a'` bounce parent (again with its original unbounded depth witness).

This is stronger than merely removing the exceptional `a'=0,1` cases: it eliminates the entire opposite-parity bounce family in each q sector. It is an exact structural theorem conditional on the displayed B2 parameterization and the residual congruences; it is not a blank-reachability exclusion. The Lean proof has not yet been compiled.


## Exact 2-adic root-index formula for the B2 depth

The q≥3 fan can be tied directly to the original residual root parameter, rather than leaving u as a free-looking parameter.

On this B2 cylinder,
`h=8+128u`. The already-proved affine root relation `w≡2496h+3073 (mod 8192)` gives
`w=6657+8192n` for some n. Since `t=39+64h=551+8192u`, substitution into the authentic residual identity yields the **exact** equation
```
18018 + 211*u + 22155*n = 20 * 2^(E-13),
E = 201 + 3360*w.
```
Indeed, the constant term in the original residual equation is
`211*551 + 1360 + 22155*6657 = 8192*18018`.

Now put `W=1113+16555u` as in the B2 parent fan. Multiplying the exact equation by 16555 and adding `211*1113` gives
```
211*W = -21*(14193007 + 17465525*n)
        + 82775*2^(E-11).
```
Both 21 and 82775 are odd. Moreover
`0 < 14193007+17465525*n < 2^(E-11)` for every natural n: the left side is less than `2^25*(n+1) ≤ 2^(n+25)`, while `E-11=190+3360*w > n+25`. The two terms on the right therefore have distinct 2-adic valuations, and 211 is odd. Consequently the exact valuation identity is
[
\boxed{v_2(1113+16555u)=v_2(14193007+17465525n).}
]

For q≥3, the mod-105 calculation already proves that `Q=(a+3)/2` is odd. Since
`W=2^(2q-3)*Q`, it follows that
[
\boxed{v_2(14193007+17465525n)=2q-3.}
]
Thus q is uniquely determined by the root index n whenever the q≥3 branch exists. In particular, q≥3 requires `n≡5 (mod 8)`. The exact q-strata are dyadic annuli: for each q, n lies in one residue class modulo `2^(2q-3)` but not the unique lift modulo `2^(2q-2)`.

The first exact classes are:

| q | Exact root-index condition |
|---:|---|
| 3 | n ≡ 5 (mod 16) |
| 4 | n ≡ 13 (mod 64) |
| 5 | n ≡ 109 (mod 256) |
| 6 | n ≡ 493 (mod 1024) |
| 7 | n ≡ 1005 (mod 4096) |
| 8 | n ≡ 11245 (mod 16384) |

This is a root-sensitive valuation normal form for the entire unbounded q≥3 B2 fan. It proves that the q-depth is not an independent search parameter: it is exactly the valuation of one odd affine function of the original root index. It does not by itself exclude the q-strata or the low q=0,1,2 branches. The derivation is arithmetic from the exact residual identity and the already source-certified affine root congruence; this new valuation identity has not yet been Lean-compiled.


## Even-u B2 branch: exact two-parent reduction and an infinite exclusion

There is a simpler source-depth bound on the B2 target whenever u is even; this does not require the mod-105 refinement.

Write
```
x = 734 + 10944*u
y = 34881 + 518816*u
W = 1113 + 16555*u
A = x+y+1 = 32*W
X = x+2*y = 70496 + 1048576*u.
```
For even u, W is odd, so A has exact 2-adic valuation 5.

Apply the complete `section_preimage_all_iff` grammar to any source predecessor of (x,y):
- a=0 is impossible because x+y is odd, while its nonexceptional output equation makes x+y even; its exceptional output is (0,4).
- a=1 is impossible: its exceptional outputs are small, its y=3 branch is too small, and its high branch would require `A=16*2^d`. Since A=32*W with W odd and W≥1113, this is impossible.
- k=0 is impossible because the output right coordinate would be 2.
- the direct branch is impossible because it outputs an even right coordinate.
- the even-a bounce branch is impossible because it makes x+y even.
- Hence only the odd-a high-bounce branch remains. Its equations simplify to
  `A=2^(d+1)*(a+3)` and `2*k+a+9+3*d=X+2`.
  Since a is odd, a+3 is even, so `2^(d+2) | A`; exact v2(A)=5 gives d≤3. Cost parity forces d even. Therefore d=0 or d=2, with the only possible source parents:
  - d=0: `P0=(17805+264880*u, 26342+391848*u)`;
  - d=2: `P1=(4449+66220*u, 33017+491178*u)`.

For every even u, P1 is odd/odd, has right coordinate ≥5, and coordinate sum
`37466+557398*u ≡ 2 (mod 4)`; the source-certified `blank_no_odd_sum_two` excludes it.

P0 is odd/even with right coordinate ≥6 and sum `44147+656728*u ≡3 (mod8)`. The source-certified `section_odd_even_iff_affine` forces its unique direct predecessor
`P2=(44145+656728*u,13170+195924*u)`.
For even u, P2 is again odd/even with sum `57315+852652*u ≡3 (mod8)`, so its unique predecessor is
`P3=(57313+852652*u,6584+97962*u)`.
P3 has even right coordinate ≥6 and sum `63897+950614*u ≡1 or 5 (mod8)`; the source-certified `blank_reach_iff_even_right` therefore forces
`P4=(63895+950614*u,3291+48981*u)`.

P4 is odd/odd with right coordinate ≥5 and sum
`67186+999595*u ≡ 2+3u (mod4)`.
Thus for `u≡0 (mod4)`, its sum is 2 modulo 4 and `blank_no_odd_sum_two` excludes it. Consequently the complete B2 parent fan is closed on the infinite cylinder
[
\boxed{u\equiv0\pmod4\quad\Longrightarrow\quad \neg CReach(734+10944u,34881+518816u).}
]
For the remaining even-u class `u≡2 (mod4)`, the same argument gives the exact reduction
`CReach(B2(u)) ↔ CReach(P4(u))`; the latter is the remaining odd/odd sum-zero state and is not excluded here.

Combining with the root-index congruence `u+r≡2 (mod8)`, the excluded cylinder `u≡0 (mod4)` corresponds to root indices `r≡2 or 6 (mod8)`. This is a paper-level composition of the complete B2 source fan with already source-certified inverse/reachability lemmas. The new composed theorem has not yet been Lean-compiled in this invocation.


## Second root-index valuation: the remaining even-u P4 state

For even u, the preceding section reduces B2 reachability to
`P4=(63895+950614u,3291+48981u)`; when u≡0 mod4 this is excluded, while u≡2 mod4 leaves P4 as the exact residual state.

Let `S4=P4.x+P4.y=67186+999595u`. Substituting the same exact residual equation
`211u+22155r+18018=20*2^(E-13)`
(with root index r and `w=6657+8192r)) gives
```
211*S4 = -7*(2570932352 + 3163718175*r)
         + 19991900*2^(E-13).
```
The coefficient 19991900 has exact 2-adic valuation 2, so the second term has valuation E-11. The affine term satisfies
`0 < 2570932352+3163718175*r < 2^(E-13)`
because it is below `2^32*(r+1)≤2^(r+32)`, while `E-13=188+3360*w>r+32`. Hence its valuation is at most E-14, strictly below E-11; the two terms have distinct 2-adic valuations. Since 7 and 211 are odd,
[
\boxed{v_2(S4)=v_2(2570932352+3163718175r).}
]

The exact root relation `u+r≡2 (mod8)` means the remaining u≡2 (mod4) sector is r≡0 or4 (mod8):
- r≡4 (mod8) gives u≡6 (mod8), hence v2(S4)=2 and the existing odd/odd low-valuation inverse applies (unless the already-recorded special odd-image obstruction fires).
- r≡0 (mod8) gives u≡2 (mod8), hence v2(S4)≥3. The displayed affine valuation now determines whether the next exact gate is the valuation-three inverse, the sum-16 two-orbit inverse, or the deeper sum-zero parent fan.

This supplies a second exact 2-adic coordinate for the residual even-u chain. It does not yet close P4; the source-parent branches after its applicable odd/odd inverse remain to be resolved and Lean-compiled.
