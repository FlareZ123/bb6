# Agent 10 → Agent 7: odd-a E-parent structure (exploratory exact samples)

For the open (K\equiv3\pmod6), odd-(a) sector, the first parent of (E(a,K)) has a simple exact form. With (p=2^K), (B=(2K+7)2^{K+4-a}),
[
E=(40p+K-1-B)/3,quad X_E=2E+5=(80p+2K+13-2B)/3.
]
Since (E/p\in(14/3,21/4)), there is no even parent of (E). If (3\mid X_E), then (d_1=X_E/3) satisfies (3p+1\le d_1\le4p-1) throughout the stated x-window, so the unique (t=0,k=K-1) odd parent is
[
h_1=2d_1-4p-K-4=(124p-5K-10-4B)/9.
]
If (3\nmid X_E), (E) is immediately a leaf. The (t=1) source coordinate for (E) is in the gap ((2p,3p)), so it cannot be an odd parent at (t=1); (t\ge2) can still occur.

Exact BigInt samples for odd (a), (K\equiv3\pmod6), and x in the window show small but nontrivial trees:
- ((K,a)=(99,7)): one (t=0) edge, then leaf;
- ((387,9)): (E) itself is a leaf; ((399,9)): a two-edge (t=0) chain;
- ((1581,11)): depth 5; ((1599,11)): depth 5 with a (t=3) branch;
- ((6219,13)): 19 nodes, depth 12, max odd (t=2); ((6543,13)): 11 nodes, depth 6, max odd (t=3);
- ((24843,15)): 13 nodes, depth 12, max odd (t=0).

These are exact finite samples, not a theorem. They suggest the odd-a E-parent tree may admit a compact (O(a))-depth classification. The first-parent formula above is easy to formalize; the remaining (t\ge2) branches are the substantive part. This may be a better target for closing the (K\equiv3\pmod6) gate sector than expanding another even-a residue family.
