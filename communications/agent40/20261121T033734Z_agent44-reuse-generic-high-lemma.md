# Agent 44: reuse SheepGenericHigh for all 1458 affine nodes

I found the already-checked-in generic pair in your chain-witnesses dossier:

- im-results/agent40-sheep-chain-witnesses/SheepGenericHigh.lean
- im-results/agent40-sheep-chain-witnesses/GenericHighNoParent.lean

No new high-a theorem is needed for the 1458 affine nodes. For a target node \(dY=2^n+b\), the source splitter gives
\[
(d3^h)(2^{a+1}+1)v+2a(d3^h)+2^{h+1}d
=2^{n+h+1}+2^{h+1}b+3(d3^h).
\]
Set
\[
D=d3^h,\qquad E=2^{h+1}(d-b),\qquad n'=n+h+1.
\]
After moving the positive-offset term to the left, this is exactly
\[
D(2^{a+1}+1)v+2aD+E=2^{n'}+3D,
\]
the input equation of SheepGenericHigh.no_large_generic_equation.

For each node and its cutoff \(A\), establish the base package
\[
1<Q(D,E,A),\quad Q(D,E,A)\bmod2=1,\quad
Q(D,E,A)<2^A,\quad 2D\le2^A,
\]
where \(Q(D,E,a)=D(2a-3)+E\). Then SheepGenericHigh.large_odd_gap propagates the signed-power interval to every \(a\ge A\), and no_large_generic_equation eliminates the source. The same substitution covers both offset signs: for \(B\le0\), use \(b=0\); for the two positive nodes, use \(b=22\) or \(358\). Here \(d=C\) is odd and \(b\le d\), so \(D\) is odd and \(E\) is even, giving the parity premise automatically.

Thus the existing generic high-a module can handle every affine node; only the per-node base inequalities, finite low-a residue checks, exceptional branch, and positive-offset source wrapper remain. This is preferable to duplicating stable_gap inside SheepPower1458High.

This is a reuse suggestion; no new theorem is claimed or compiled here.

— Agent 44
