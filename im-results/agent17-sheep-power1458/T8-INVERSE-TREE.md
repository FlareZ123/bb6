# Seventh Sheep stratum: two-node inverse-tree progression

**Agent 17, 20 November 2026. Preferred candidate for independent audit and Lean formalization.**

This extends the exact direct-parent census in this directory. It uses the original even-return source relation at every inverse step, not a finite-horizon trajectory search.

## Accepted subfamily theorem

Let
\[
T=10\,475\,665\,200
=2^4\cdot3^4\cdot5^2\cdot7\cdot11\cdot13\cdot17\cdot19.
\]
The exact affine inverse-tree certificate supports
\[
\boxed{\forall k\ge0,\quad
\neg\operatorname{EvenReach}
\left(10,2^{1458(8+Tk)}\right).}
\]
Equivalently, the exponent indices are
\[
j=11\,664+15\,273\,519\,861\,600\,k.
\]

This one-class subfamily is now included in the compiled `SheepPower1458.noEvenReachFiveFamilies` theorem from [CI 45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209), with transitive axiom profile `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. It remains a partial exclusion, not a Sheep machine or BB(6) decision. Keep it in `im-results/`.

## Why the direct-parent gate does not cover this class

The existing direct-parent theorem `blank_even_cannot_hit_seventh` requires
\[
3\nmid t,\quad4\mid t,\quad
t\not\equiv5\pmod7,\quad
t\not\equiv1\pmod9,\quad
t\not\equiv8\pmod{15}.
\]
Here (t\equiv8\pmod T), and (T) is divisible by 1260. Thus (t\equiv8\pmod{1260}), and the final condition leaves one genuine generic direct parent with hidden length (h=7) and source valuation (a=4). The proof closes its ancestry rather than ruling out the first edge.

## Original-source inverse equations

For every authentic even edge `EvenEdge x y`, Agent 14's `SheepEvenSourceAlgebra.even_edge_to_algebra` gives exactly:

- Generic: (y=1+3^h u), (u) odd, (x=2^a v), (a\ge1), (v\ge5) odd, and
  \[
  (2^{a+1}+1)v=2^{h+1}u+3-2a.
  \]
- Exceptional: (y=1+3^h u), (u) odd, (x=3\cdot2^a), and
  \[
  2^h u=3\cdot2^a+a+2.
  \]

No power-target hypothesis on (y) is needed; this matters for the intermediate node.

## The unique first parent

For (Y_0(t)=2^{1458t}), the complete direct-parent census on (t\equiv8\pmod{1260}) has exactly one hit:
\[
h=7,\qquad a=4.
\]
Its generic equation is
\[
3^7(2^5+1)v+
\bigl(3^7(2\cdot4-3)+2^8\bigr)
=2^{1458t+8},
\]
or
\[
72\,171v+11\,191=2^{1458t+8}.
\]
The unique parent is (x=16v), represented by
\[
Y_1(t)=16v
=\frac{2^{1458t+12}-179\,056}{72\,171}.
\]
At (t=8), (Y_1(8)) is a positive even integer greater than 10 and (v_3(Y_1(8)-1)=0). The period certificate freezes this valuation throughout (t\equiv8\pmod T).

## No predecessor of the second node

Since (v_3(Y_1(t)-1)=0), the only possible hidden length is (h=0). Its generic source equation is
\[
72\,171(2^{a+1}+1)w+
(144\,342a+285\,941)
=2^{1458t+13}.
\]
The residual (K(a)=144342a+285941) is odd. At cutoff (A=22),
\[
1<K(22)=3\,461\,465<2^{22},
\qquad 2\cdot72\,171\le2^{22}.
\]
Since (K(a+1)=K(a)+144342), these bounds persist for every (a\ge22). The existing `SheepOddGap.no_power_signed_small_odd` excludes every such (a).

The remaining 21 valuations (1\le a<22) are all excluded by exact modular arithmetic. Together with the 70 root-level rows, the certificate checks 91 moduli. Thus (Y_1(t)) has no generic predecessor for any (t\equiv8\pmod T).

## Exceptional source exclusion

For an exceptional parent (3\cdot2^a), the equation becomes
\[
2^{1458t+s+h}=3D\,2^a+L(a),
\quad L(a)=D(a+2)+2^h(C-B),
\]
where (Y(t)=(2^{1458t+s}+B)/C) and (D=C3^h).

For each of the nine node/hidden-length pairs, the certificate supplies a cutoff (S) with
\[
1<L(S)<2^S,\qquad D\le2^S.
\]
The recurrence (L(a+1)=L(a)+D) propagates the bounds. If (a\le1458t+s+h), the equation forces (2^a\mid L(a)), impossible. If (a) is larger, its right side exceeds the left side. For every smaller (a<S), the exact certificate verifies that the right side is already below the left side at (t=8), and the left side increases thereafter. No exceptional parent exists at either node.

The cutoffs are:

| Node | Generic (A) by (h) | Exceptional (S) by (h) |
|---:|---|---|
| 0 | 0:2, 1:5, 2:7, 3:9, 4:11, 5:13, 6:15, 7:16 | 0:3, 1:5, 2:7, 3:9, 4:10, 5:12, 6:14, 7:16 |
| 1 | 0:22 | 0:21 |

## Exact period certificate

For each node, hidden length, and generic valuation below its cutoff, the modular test is modulo
\[
N=C3^h(2^{a+1}+1).
\]
The certificate computes (o_N=\operatorname{ord}_N(2)) and period (p_N=o_N/\gcd(o_N,1458)), plus periods freezing (v_3(Y(t)-1)).

- 91 exact generic modular periods;
- 2 valuation-freezing periods (3 for the root, 9 for the second node);
- LCM of tree periods: (2\,095\,133\,040);
- LCM of the 28 prior E-cone progression periods: (1\,178\,100);
- common period: (T=10\,475\,665\,200).

The certificate checks (2^{1458T}\equiv1\pmod N) for all 91 moduli and for both valuation moduli. Hence the complete parent classification is constant for (t=8+Tk).

All 28 earlier E-cone progressions are disjoint: the base exponent (11\,664) is not in any old residue class, and (T) is a multiple of every (p/\gcd(p,1458)).

## Complete inverse graph and contradiction

The entire inverse graph is
\[
Y_0(t)=2^{1458t}
\quad\xrightarrow{(h=7,a=4)}\quad
Y_1(t)=\frac{2^{1458t+12}-179\,056}{72\,171}.
\]
There are exactly two nodes and one edge. (Y_1(t)) has neither a generic nor an exceptional predecessor.

If (Y_0(t)) were in `EvenReach 10`, the last-edge theorem would yield a genuine earlier even state (x) with `EvenReach 10 x` and an original `EvenEdge x (Y_0(t))`. Even reachability preserves evenness, so the original source splitter applies. The complete classification forces (x=Y_1(t)). Applying the same last-edge argument to (Y_1(t)) is impossible because it has no predecessor of either source type. Thus the target is not blank-reachable.

This is an ancestry proof, not a bounded trajectory simulation.

## Scope and next step

The progression has density (1/15\,273\,519\,861\,600) among all exponent indices. It is disjoint from the 28 earlier E-cone progressions and from the (v_3(j)=3,4,7) strata. It does not decide the Sheep machine or BB(6).

The highest-value next action is independent review and Lean formalization using:
- `im-results/agent14-sheep-even-inverse/SheepEvenReachInverse.lean` for last-edge reachability;
- `im-results/agent14-sheep-even-inverse/SheepEvenSourceAlgebra.lean` for the arbitrary-edge generic/exceptional split;
- `im-results/agent40-sheep-third-preimages/SheepOddGap.lean` for the uniform generic cutoff.

The local shell/Python tools returned platform `ClientError` during this invocation, so this candidate has not been locally compiled. Do not promote it to `results/` or claim formal verification until Lean 4.36.0-rc2 compiles the theorem against the pinned original source and `#print axioms` shows no `sorryAx`.
