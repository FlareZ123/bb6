# Agent 7 addendum: exact 486-shift law for the omitted G-parent branch

For the high (Y=2h+5) branch, the omitted (t=0) parent is
[
g=Y/3,qquad G=2g-2p-K-3,qquad Z=2G+5,
]
where (p=2^K), (X=T/3),
[
T=80p+2K+13-2(2K+7)2^{K+4-a},quad
h=2(X/3)-4p-K-4,quad Y=2h+5.
]
On the two non-high third-lift residues, (v_3(Y)=2), so (g) is an integer and the (t=0) edge (G\to h) is source-valid by the existing (3/2<g/p<2) bound.

There is a further exact shift law. Since (2^{486}\equiv1\pmod{729}), and (e=K+4-a) is even,
[
egin{aligned}
T(K+486)-T(K)
&\equiv972-1944\cdot2^e\pmod{729}\
&\equiv243-486\equiv486\pmod{729},
end{aligned}
]
using (2^e\equiv1\pmod3). Dividing successively through the definitions gives
[
X(K+486)\equiv X(K)+162\pmod{243},
]
[
h(K+486)\equiv h(K)+27\pmod{81},qquad
Y(K+486)\equiv Y(K)+54\pmod{81},
]
[
g(K+486)\equiv g(K)+18\pmod{27},qquad
G(K+486)\equiv G(K)+9\pmod{27},
]
and therefore
[
oxed{Z(K+486)\equiv Z(K)+18\pmod{27}.}
]
Thus the three (K\bmod1458) lifts of a fixed (K\bmod486) class cycle (Z\bmod27) by (+18). If (9\mid Z), the three values are (0,9,18) in some order: two lifts have (v_3(Z)=2), and one has (v_3(Z)\ge3). This is the next exact 3-adic lift after the omitted (G)-parent, not a closure of that branch.

An independent finite residue calculation over odd (a\bmod162) and the two non-high (Y\bmod27\in\{9,18\}) lifts gives (Z\bmod27) uniformly distributed over (0,3,6,\ldots,24), 18 occurrences each. In particular, 54/162 cases have (9\mid Z), consistent with the shift-law split. The computation is only a residue audit; the displayed shift law is algebraic.

This suggests the next branch analysis should track all (t<v_3(Z)), not only the maximal valuation (t=v_3(Z)-1). For (r=Z/(3p)), the (t)-th odd source parameter has normalized height ((2/3)^t r), and it may land in a different dyadic source band for several separated (t)-values. The 486-shift law gives an exact residue recursion for those further valuations.
