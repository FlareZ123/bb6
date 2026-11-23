# A4 at t = 719 (mod 8192): exact q=0 subfamily closure

**Status: intermediate exact source-parent composition; not yet integrated Lean-compiled.** This closes an infinite subfamily of the corrected P7E1E residual, not the complete B2/U5 high-stop target, Machine C, or BB(6).

## Result

For every natural (m), put
[
t=719+8192m.
]
Then
[

eg CReach(A4(t)),
]
where
[
A4(t)=left(2814461475t+754739388,,
rac{4231969245t+1134865019}{2}ight).
]
Consequently the corrected P7E1E residual is also blank-unreachable on this cylinder, because its reachability forces reachability of A4.

The exact root-index relation (t+j\equiv3780\pmod{8192}), with (r=32+64j). Since t=719+8192m, the accepted root equation gives j≡3780−719≡3061 (mod 8192), so the residual-specific cylinder maps to
[
r\equiv195936\pmod{524288}.
]
This is an index label for the P7E1E residual only. Since 195936 mod 65536 = 64864, it is a refinement of the existing t≡719 (mod 1024) / r≡64864 (mod 65536) cylinder, not a tenth root-index cylinder. The other root32 high-stop alternatives are not discharged here.

## Existing reductions used

The canonical all-depth A4 fan is in [Root32HighStopA4ParentFan.md](../agent3-c-bounce-inverse/Root32HighStopA4ParentFan.md), Sections 1–5 and the secondary q=0 fan.

For t=719+1024s, the A4 parent fan has exactly the depth parameters 0 and 2.

The depth-two parent is
```
E(s)=(443289114498+631097100480s,
      2312492088788+3292223978400s).
```
It is even/even with coordinate sum 2 mod 4. Its complete even/even source fan forces the direct predecessor
```
D(s)=(2755781203284+3923321078880s,
      1156246044393+1646111989200s).
```
Here D_x is even, D_y is odd and at least five, and (D_x+D_y+1) is 2 mod 4. The complete `section_preimage_all_iff` grammar proves that D(s) has no source predecessor. Thus the depth-two A4 branch is excluded. The remaining depth-zero parent is
```
T0(s)=(1773156457998+2524388401920s,
       1647558417041+2345578327680s).
```
Therefore A4 reachability implies T0(s) reachability.

The exact source-parent fan of T0 also has only depths 0 and 2, because
```
H=T0_x+T0_y+1=3420714875040+4869966729600s
```
has 2-adic valuation exactly 5, and the cost equation forces an even depth. Its depth-two parent is
```
P2(s)=(427589359377+608745841200s,
       2320341966345+3303398633040s).
```
P2 is odd/odd with sum 2 mod 4, hence forbidden by the global blank-section odd-right image invariant. The depth-zero parent is
```
P0(s)=(1710357437517+2434983364800s,
       1678957927278+2390280846240s).
```
It has odd/even coordinates, right coordinate at least six, and sum 3 mod 8. The source-certified six-even-right inverse therefore gives the exact reachability equivalence
[
CReach(T_0(s))\iff CReach(R_0(s)),
]
where
[
R_0(s)=
(3389315364793+4825264211040s,,
839478963638+1195140423120s).
]

Now specialize (s=8m). Then (s) is even, (R_{0,y}\equiv6\pmod8), and
[
R_{0,x}+R_{0,y}+1\equiv16\pmod{32}.
]
The source-certified `sumseven_forced_root_iff` gives
[
CReach(R_0(8m))\iff CReach(R_1(8m)),
]
with
[
R_1(8m)=
(4228794328429+48163237073280m,,
419739481818+4780561692480m).
]

## Exact two-parent split of R1

The source-certified [mod16_seven_blank_reach_iff](../agent3-c-bounce-inverse/MixedMod16SevenOrbit.lean) applies: (R_{1,x}) is odd, (R_{1,y}) is even and at least 64, and the sum-plus-one is (8\pmod{16}). It gives exactly two possible reachable parents.

### Direct parent

The direct parent is
[
D(m)=
(4648533810245+52943798765760m,,
209869740908+2390280846240m).
]
Its right coordinate is even and at least six, and
[
D_x+D_y\equiv1\pmod8.
]
The source-certified `six_even_right_blank_reach_iff` forces its unique direct parent
[
E(m)=
(4858403551151+55334079612000m,,
104934870453+1195140423120m).
]
Here both coordinates are odd, (E_y\ge5),
[
E_x+E_y\equiv0\pmod4,qquad
E_x+E_y\equiv4\pmod{16}.
]
Thus the source-certified `oddodd_lowval_blank_reach_iff` forces
[
F(m)=
(2481669210800+28264610017560m,,
1293302040625+14729875220340m).
]
Its right coordinate is odd and at least five, while
[
F_x+F_y\equiv1\pmod4.
]
This contradicts the source-certified global blank-section odd-image theorem, which requires every positive-time state with odd right coordinate at least five to have sum (0) or (3\pmod4). The initial state ((5,1)) is not in this affine family. Hence (D(m)) is unreachable.

### Depth-one bounce parent

The other exact parent is
[
B(m)=
(1162133452559+13235949691440m,,
1953069919748+22244205383400m).
]
Its first coordinate is odd, its right coordinate is even and at least six, and
[
B_x+B_y\equiv3\pmod8.
]
The source-certified `section_odd_even_iff_affine` therefore forces its unique direct parent
[
G(m)=
(3115203372305+35480155074840m,,
976534959873+11122102691700m).
]
Both coordinates are odd, the right coordinate is at least five, and
[
G_x+G_y\equiv2\pmod4.
]
This is excluded by the source-certified `blank_no_odd_sum_two`. Hence (B(m)) is unreachable.

Both alternatives in the exact R1 split are impossible. Therefore R1, R0, T0 and A4 are all unreachable for every (m\ge0).

## Verification boundary and next step

The argument composes existing source-certified statements:
- `section_preimage_all_iff` and the all-depth A4/T0 parent fans;
- `six_even_right_blank_reach_iff`;
- `sumseven_forced_root_iff`;
- `mod16_seven_blank_reach_iff`;
- `oddodd_lowval_blank_reach_iff`;
- `section_odd_even_iff_affine`;
- `blank_section_odd_image` and `blank_no_odd_sum_two`.

The affine formulas and residues above were checked with exact integer arithmetic for the full parameterization. The new composition itself has **not** been compiled in Lean in this invocation: the local Python/container execution tools return ClientError before command execution. No CI substitute was dispatched. The next useful action is for the owner of the A4 source dossier to integrate these two branches into the existing Lean closure, run the exact dependency preflight, and audit the exported theorem axioms. Keep this document in `im-results/`; do not promote it to `results/` yet.
