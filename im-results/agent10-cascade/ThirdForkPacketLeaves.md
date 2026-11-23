# Every surviving #746 gate has a linear family of genuine but parentless third-valuation feeders

**Status, 23 November 2026:** new **paper-level all-index composition** of the exact original-source first-reset grammar, the previously source-certified [unique Hensel depth residue](../agent7-fatal-density/RayDepthResidue.lean), and the source-certified [third-valuation root-gap theorem](RayTThreeGap.lean). The new *universal 162-index packet counting and geometric conjunction* has not been compiled as a single Lean theorem. This is an authentic source-**inverse graph** theorem, **not** a blank-root decision, #746 nonhalting proof, or BB(6) upper bound.

## Quantified theorem

For every gate candidate `n≥257`, `n mod 6∈{4,5}`, let
[
p=2^n,qquad c=2n+3,qquad a=lfloorlog_2 cfloor,qquad J=n-a,
]
and `u_j=4p+n−1−c2^j` for `0≤j≤J`. These are the actual #746 fatal `u_0=4p−n−4` canonical even-ray heights. Define
[
B=leftlfloor rac{J-13}{162}ightfloor.
]
For **every** `b=0,…,B−1`, among the **81 even ray indices**
[
jin{162b, 162b+2,ldots,162b+160}
]
there are exactly three with `81∣X_j:=2u_j+5`, and these three have `X_j/81mod 3` equal to `0,1,2` **in some order**.

All three have a distinct genuine **t=3 odd** predecessor `h_j`, with
[
d_j=X_j/81,quad 16d_j=p+h_j+n+2,qquad
operatorname{ResetParent}(h_j,u_j).
]
Every such `h_j` lies strictly in the gap
[
p/2 < h_j < 3p/4,
]
so **none has an even ResetParent predecessor**. In each packet **at least two** of these three `h_j` also have `h_jmod 3≠2`; these two have **no odd ResetParent predecessor either**, and therefore are **parentless in the complete, untruncated source-C reset graph**. All these parentless `h_j` are pairwise distinct across all packets.

Thus, for every surviving `n≥257`, the canonical ray has at least
[
oxed{2,leftlfloor (n-lfloorlog_2(2n+3)floor-13)/162ightfloor}
]
**distinct, genuine t=3 source predecessors with no own predecessors**. This is a **uniform linear-in-n** lower bound on explicitly prunable third-valuation branches, not a lower bound on actually rooted branches. The third residue class can require deeper odd-valuation recursion.

## Proof: exact modular three-packet

Take `j_0=depthResidue(n,3)`, the computable index certified in [`RayDepthResidue.lean`](../agent7-fatal-density/RayDepthResidue.lean). The source theorem `depthResidue_lt` gives `j_0<depthPeriod(3)=54`, and `depthResidue_iff` says `3^4=81∣signedZ(n,j_0)=X_(j_0)` on the physical ray. By `2^54≡82=1+81` and `2^108≡163=1+162` modulo 243,
[
X_{j_0+54t}equiv X_{j_0}-81tcdot 2c2^{j_0}pmod{243}
qquad(t=0,1,2).
]
Since `3∤c`, the coefficient `2c2^{j_0}` is a unit modulo 3. Therefore `X_{j_0+54t}/81mod3` runs through `0,1,2` precisely once. All three indices remain even and below 162. Conversely, the unique-index Hensel congruence `depthResidue_iff(n,3,j)` says that there are **no other** even j in this packet with `81∣X_j`.

As `2^162≡1 (mod243)`, the three residues and their quotient classes repeat in **every** packet translated by 162. The same uniqueness holds for every block.

## Proof: genuine source band, gap, and no-parent residue

Throughout these complete packets, `0≤j≤162B−2≤J−15`. Since `c2^J<2p`, `c2^j<p/4096`. The exact numerator identity
[
X_j=8p+2n+3-2c2^j
]
gives `8p-p/2048<X_j<8p+2n+3`. As `n≥257`, `p` dwarfs `n`. For `81∣X_j`, put `d_j=X_j/81` (necessarily positive and odd). Direct multiplication gives the source strict band at scale `k=n−3`:
[
6cdot2^{n-3}+1le8d_jle8cdot2^{n-3}-1.
]
The odd source-output equation `2u_j+5=3^4d_j` holds by definition. Defining `h_j=16d_j-p-n-2` gives `16d_j=8cdot2^{n-3}+h_j+(n-3)+5`, and the lower bound makes `h_j≥0`. These three equations are exactly the **genuine**, all-valuation `ResetParent` odd arm, with t=3. No simulated tape reachability or truncated valuation argument is used.

The same bounds give `p/2<h_j<3p/4`, so its height lies between the disjoint even-parent target bands (the adjacent bands terminate at `p/2−3` and begin at `3p/4−1`). This is the source-checked gap in [`RayTThreeGap.ray_tthree_parent_gap`](RayTThreeGap.lean). The even arm of `ResetParent` is impossible for every `h_j`.

For the odd arm, `2h_j+5` must be divisible by three, requiring `h_j≡2 (mod3)`. The source-sector lemma [`pow_sector_mod_three`](../agent7-fatal-density/RayDepthHensel.lean) gives `p≡n (mod3)`, hence the exact source equation yields
[
h_jequivegin{cases}
d_j-1&nequiv4pmod6,\
d_j&nequiv5pmod6
end{cases}pmod3.
]
Thus when `n≡4`, only `d_j≡0` could have an odd parent; when `n≡5`, only `d_j≡2` could have an odd parent. Of the exactly three `d_jmod3` classes in each packet, **two** fail this necessary gate. Those two **have no ResetParent at all**. The weaker blank-root consequence for a given offray parent is already a source-compiled lemma [`ray_tthree_parent_dead`](RayTThreeGap.lean).

Finally, `j↦X_j` strictly decreases, so the associated `d_j` and `h_j` are all distinct across packets. The number of explicitly source-parentless offray parents is at least `2B`. There is no conclusion that `u_j` itself is rooted, and no finite-parent-tree argument has been extended to the entire fatal gate.

## Exact reproducible checks and integration

The dependency-free [`third_fork_packet_leaves.mjs`](third_fork_packet_leaves.mjs) checks every j in all complete packets using BigInt, verifies the *full* odd source band and algebraic reset-parent equations, checks both adjacent even-band gap inequalities and `h_j mod3`, and requires exactly three genuine t=3 parents and exactly two parentless certified children per packet. Independently evaluated results in the JS runtime:

| gate index n | J | full 162-index packets B | distinct certified parentless t=3 feeders |
|---:|---:|---:|---:|
| 257 | 248 | 1 | 2 |
| 262 | 253 | 1 | 2 |
| 263 | 254 | 1 | 2 |
| 1000 | 990 | 6 | 12 |
| 10000 | 9986 | 61 | 122 |

For full Lean acceptance, compose `depthResidue_iff` (or `RayDepthPhysical.admissible_ray_valuation_iff`), the existing `signedZ_shift_digit_mod` with `k=3`, and `RayTThreeGap.ray_tthree_parent_gap` against an exact original ray bound for `j≤J−15`. The only genuinely new algebraic branch is the three-class mod-243 quotient permutation and its counting across complete packets. Reuse existing modules; no new workflow file is warranted. This is a distinct result from the [uniform logarithmic **fan-in** theorem](EveryGateRayFanin.md): there, many valid parents coexist at one ray vertex; here, **two synthetic third-valuation parents are dead in each period**, across linearly many vertices.
