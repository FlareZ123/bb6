# Robust linear-gap source-cone synchronization non-closure for #623

**Status:** source-faithful **all-depth mathematical counterfamily** strengthening [InfiniteConeSyncNonclosure.md](InfiniteConeSyncNonclosure.md). It shows universal full-rectangle S-window synchronization is not inductive even under **pointwise linear separation** from the terminal-balance line on both sides of an original-source transition, and even with the previously proposed strong old-ray square-gap condition. These states are **synthetic**, not asserted blank-root-reachable. The combined theorem is an exact paper derivation from the existing source-certified LE drain identities, **not** a single source-imported Lean proof.

## Theorem

For **every** integer \(\ell\ge30\), there is an **actual, successful** machine #623 high-level LE→LE transition
\[
\boxed{D(4q+c,q)\longrightarrow D(a',d')}
\tag{1}
\]
with both endpoints in original-source newAffineCone, **the same mass-indexed correction-only S-window depth** \(\ell'_S=\ell_S=\ell\), and the following simultaneous properties:

- Source window word \((x,y)=(N,1)\) synchronizes both full carry rectangles, where \(N=3^{n-1}\) and \(n=j-k-4\). The target word does **not** synchronize its full right rectangle: \([x'+y']_N\in\{0,-1\}\).
- Writing \(p=|a-d|,\ q=\min(a,d),\ g=p-3q\), and analogously \(g',q'\) at the target, both states are **uniformly far from terminal cancellation**:
  \[
  \boxed{g>\frac4{81}q>0,\qquad g'\le-2q'.}
  \tag{2}
  \]
- Their conventional LE old-ray distances \(h=g-5,h'=g'-5\) both satisfy
  \[
  \boxed{h^2>5q,\qquad (h')^2>5q'.}
  \tag{3}
  \]
  Thus merely adding the previously observed square-gap invariant cannot repair a universal sync-induction claim.

For the least progression representatives specified below, moreover,
\[
\boxed{\lim_{\ell\to\infty}g/q=10/79,\qquad
\lim_{\ell\to\infty}|g'|/q'=701/237.}
\tag{4}
\]
This failure is a macroscopic root-ratio phenomenon, not a logarithmic narrow-strip anomaly.

## 1. A large congruence-compatible source gap

Put \(\tau(h)=(3^h-1)/2\). Fix \(\ell\ge30\) and set
\[
B=34\ell+122,\quad
k=\min\{i:3^i>B\},\quad j=\min\{i:3^i>B^3\},
\]
\[
P=3^{k+2},\quad M=3^{j-k-4},\quad N=M/3,\quad
H=PN=3^{j-3},\quad \sigma=(P-1)/2.
\]
We have \(k\ge7,n=j-k-4\ge8\), and \(H=PN\) with \(N\ge3^7\). Choose \(t_0\in\{1,4\}\) so that \(t_0\equiv1\pmod3\) and \(Ht_0+\sigma\equiv0\pmod2\) (unique since \(H\) is odd). Define
\[
c_r=\frac{H(t_0+6r)+\sigma}{2},\quad r\in\mathbb N.
\]
These are integers with step \(3H\), first value \(0<c_0<3H\), and
\(2c_r\equiv H+\sigma\pmod{3H}\).
Choose the **least** \(c=c_r\ge3^{\ell-5}\). It obeys
\[
\boxed{3^{\ell-5}\le c<3^{\ell-5}+3H<3^{\ell-4}.}
\tag{5}
\]
For the last inequality, minimality of \(j\) gives
\(3H\le B^3/3\). The elementary bound
\(B^3<6\cdot3^{\ell-5}\) holds for \(\ell=30\)
(\(1142^3<6\cdot3^{25}\)) and persists, since
\((B+34)^3/B^3\le(1+34/1142)^3<3\), whereas
\(3^{\ell-5}\) triples at every step. Thus (5) is valid for all \(\ell\ge30\).

## 2. Select an even q with unchanged source/target mass depth

Choose q in the interval
\[
\boxed{
\frac{\tau(\ell-1)-c-3}{5}<q\le
\frac{\tau(\ell)-c-3\ell-9}{6}.
}
\tag{6}
\]
Its length is exactly
\[
\Delta=
\frac{9\cdot3^{\ell-1}+1}{60}
+\frac c{30}-\frac{\ell}{2}-\frac9{10}.
\tag{7}
\]
For every \(\ell\ge30\), \(\Delta>2H\) and the left endpoint is positive. This follows already from the weaker
\((9/60)3^{\ell-1}-\ell/2-9/10>(2/9)B^3\):
check it at 30, then note the exponential term triples per step,
\(B^3\) grows by a factor strictly below 3, and the negative linear
part changes by only \(1/2\). Here \(2H\le(2/9)B^3\).

Choose \(u_0\in\{1,3\}\) such that \(1+Mu_0\equiv0\pmod4\), and set
\[
q_r=\frac{3^{k+1}(1+M(u_0+4r))}{2},\quad r\in\mathbb N.
\]
These are positive **even** integers, have gap \(2H\), and satisfy
\(6q_r=P(1+M(u_0+4r))\). The first lies in \((0,2H)\), so the interval (6), of length \(>2H\), contains one. Choose the **least such q strictly above the left endpoint**. It obeys
\[
q<\tau(\ell)/6<3^\ell/12,\qquad
q>2c,\qquad
c>\frac4{81}q.
\tag{8}
\]
Indeed, (5) and (6) give \(q>2c\) because
\(\tau(\ell-1)>11\cdot3^{\ell-4}+3\); and
\(c/q>3^{\ell-5}/(3^\ell/12)=4/81\).

## 3. Exact original-source transition and both cone budgets

The source \(D(4q+c,q)\) lies in the original far-left-even cone: \(q\) is even, \(a-d=3q+c\), and \(q+2\le\tau(3q+c-2)\).

The **original** high-level transition rule is exactly
\[
\mathrm{highLevelNext}(D(4q+c,q))
=\mathrm{drainB}(3q+c-2,q+2,2).
\]
For the successful drain let \(L\) be the total ternary valuation length, \(D=L-2n_2\) the signed first-counter drop and \(R=n_1+n_2\) the full evaluator-call count. Established source-certified digit identities give
\[
\boxed{(a',d')=(3q+c-2-D,\quad3q+8+2D+2R).}
\tag{9}
\]
As \(2q+3<3^\ell\), its valuation depth is \(L\le\ell\) and
\[
|D|\le\ell,\quad0\le R\le\ell,\quad D+2R=L+2n_1\ge0.
\tag{10}
\]
Put \(T=3D+2R+10\), so \(|T|\le5\ell+10\). Then
\[
p':=a'-d'=c-T>0
\]
and \(d'=q'\) is even, so the target is also LE. In fact
\[
q'\le3q+4\ell+8,\quad p'\ge c-5\ell-10.
\]
Our \(c\ge3^{\ell-5}\) gives \(p'-2\ge\ell+2\), while \(q<\tau(\ell)/6\) yields \(q'+2\le\tau(\ell+2)\). Hence the **original target LE cone budget** \(q'+2\le\tau(p'-2)\) holds.

The exact mass update is
\[
S'=a'+d'=6q+c+D+2R+6>S=5q+c.
\]
The source depth is exactly \(\ell\) because \(S+3>\tau(\ell-1)\) by (6). The upper inequality in (6) and (10) give
\[
S'+3\le6q+c+3\ell+9\le\tau(\ell).
\]
Thus
\[
\boxed{\ell'_S=\ell_S=\ell;}
\tag{11}
\]
in particular **the S-window cut does not move at all**: both endpoints use the same \(P,M,N\).

## 4. Source synchronization and unavoidable target failure

For input LE, \(p=3q+c\), global signed coordinates are
\[
X=2(p-3q)-10=2c-10=Ht+\sigma-10,\quad
Y=6q=P(1+Mu),
\]
with \(t\equiv1\pmod3\). As \(0<\sigma-10<P\), the exact input S-window word is
\[
\boxed{(x,y)=(N,1)\pmod M.}
\]
The four exact full-rectangle synchronization residues are
\[
[x-3y]_M=N-3,\quad[4x+3y]_M=N+3,\quad
[y]_N=1,\quad[x+y]_N=1,
\]
all safe for \(n\ge8\).

The target global signed **sum** is
\[
V'=X'+Y'=2p'-10=Ht+\sigma-2T-10.
\]
Our bounds \(P>9B>306\ell+1098\) and \(|T|\le5\ell+10\) imply
\[
0<\sigma-2T-10<P.
\]
Therefore \([\lfloor V'/P\rfloor]_N=0\). The exact Euclidean low-boundary carry identity
\[
\lfloor X'/P\rfloor+\lfloor Y'/P\rfloor
=\lfloor(X'+Y')/P\rfloor-c_V,\qquad c_V\in\{0,1\}
\]
forces the *actual target digit word*
\[
\boxed{[x'+y']_N\in\{0,N-1\},}
\]
**forbidden by the full right-rectangle synchronization criterion**. This proves the theorem without needing individual drain digit values.

## 5. Both states avoid terminal balance by a linear margin

Input \(g=p-3q=c>4q/81\) by (8).
Target \(p'=c-T<q'\) because \(q>2c\),
\(q'\ge3q-2\ell+8\), \(p'\le c+5\ell+10\), and
\(c\ge3^{\ell-5}\gg7\ell+2\). Hence
\[
g'=p'-3q'\le-2q'.
\]
For the old-ray distances \(h=g-5,h'=g'-5\), the source has
\(h\ge c/2\) and
\(h^2\ge3^{2\ell-10}/4>5q\), using
\(q<3^\ell/12\) and \(\ell\ge30\).
Target has \(|h'|\ge2q'\), and thus \((h')^2>5q'\) since \(q'\ge2\).
**Both endpoints satisfy the stronger empirical square-gap condition**, despite target synchronization failure.

Finally the least representatives satisfy
\(c=3^{\ell-5}+O(H)=3^{\ell-5}+O(\ell^3)\) and
\(q=(\tau(\ell-1)-c-3)/5+O(H)
=(79/10)3^{\ell-5}+O(\ell^3)\).
The source drain corrections are \(O(\ell)\), so
\[
g/q\to10/79,\quad
|g'|/q'=(3q'-p')/q'\to3-\frac{10}{237}=\frac{701}{237}.
\]

## Reproducer, example and scope

[verify_robust_cone_sync_nonclosure.js](verify_robust_cone_sync_nonclosure.js) independently executes the **original** evalA and drainB rules using BigInt and checks **all 71 depths \(\ell=30,\ldots,100\)**, the cone budgets, common mass cut, all sync residues, and both strong gap inequalities. These checks corroborate—not replace—the all-depth proof.

At \(\ell=30\):
\[
D(27621983192357,6693657501978)
\longrightarrow
D(20928325690361,20080972505994).
\]
Both are LE-cone states of exact mass depth 30. Window words are
\((6561,1)\) and \((6558,3)\); the input synchronizes, the output sum
is \(0\bmod6561\), so the target right rectangle fails. Gap ratios:
\(g/q\approx0.12659046\), \(|g'|/q'\approx2.95780318\).

**Implication:** neither terminal-window separation nor the quantitative
quadratic or even uniform linear distance from the terminal line can
supply the missing forward-invariance condition for **all** canonical
cone states. A blank-root result requires a genuinely root-specific
source-history/digit-language invariant. This construction is **not** a
blank-root orbit counterexample and yields no BB(6) bound.
