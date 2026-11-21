# D0E inverse-chain arithmetic and residual E7 branch

**Current status (21 November 2026):** the exact affine inverse chain and root-index arithmetic are Lean-checked in `D0EInverseArithmetic.lean`; the original-source parent composition for the R10592 class is an uncompiled intermediate draft in `Root32HighStopR10592Core.lean`. This is not a nonhalting proof or an accepted high-stop exclusion. The draft now uses the corrected three-residual P7 theorem and the accepted A4Core t≡31 (mod32) result; it does not rely on the older two-residual wrapper. The full nine-class union remains open.

## 1. Root32 parameter and direct inverse chain

The q=0 root32 bridge gives
[
u=1802+6720t.
]
The surviving direct-parent branch of (D_0(u)) is
[
D0E(u)=(218624u+14700,;414976u+27902).
]

Define
[
operatorname{dp}(x,y)=(x+y-2,(y-2)/2).
]
The Lean file `D0EInverseArithmetic.lean` proves the exact chain
[
D0E(u)	o d_1(u)	o d_2(u)	ocdots	o d_7(u)	o d_8(u),
]
where each arrow is (operatorname{dp}). For (u=1802+6720t), the seven intermediate states (d_0,ldots,d_6) are even/even, have right coordinate at least six, and have coordinate sum (2pmod4). The complete even-even parent fan therefore forces the direct parent at each of these seven stages: the zero-left branch has sum divisible by eight, and an even-a bounce has sum divisible by four.

## 2. The terminal fork and E7 reduction

The state immediately before (d_8) is
[
d_7(t)=(7002858240t+1877919828,;21786240t+5842300).
]
Its sum is
[
d_{7,x}+d_{7,y}=8S,qquad S=878080560t+235470266,
]
with (Sequiv2pmod4) and (S>2). The complete even-even sum-zero parent theorem leaves exactly two alternatives:

- direct parent
  [
  d_8(t)=(7024644480t+1883762126,;10893120t+2921149);
  ]
- depth-one even-a bounce parent
  [
  E7(t)=(1756161120t+470940530,;2645134800t+709331944).
  ]

The direct branch (d_8) is source-unreachable. Its coordinates are even/odd, its sum is divisible by three, and
[
d_{8,x}+d_{8,y}+1equiv4pmod8.
]
The exact even-odd-three-divisible inverse forces an odd-a, even-depth parent. Since the sum-plus-one has exact 2-adic valuation two, that depth is zero, and the unique parent is
[
(3517768800t+943341635,;1764330960t+473131391).
]
Both counters are odd, the right counter is at least five, and their sum is (2pmod4). The original-source odd-image sum-two theorem excludes it. Hence
[
D0E(u)	ext{ reachable}Longrightarrow E7(t)	ext{ reachable}.
]
This is a reduction, not an exclusion of D0E.

## 3. The next E7 inverse and root-index localization

Since (E7(t)) is even/even with sum (2pmod4), its only source parent is
[
P(t)=(4401295920t+1180272472,;1322567400t+354665971).
]
The target (P(t)) is even/odd and has
[
P_x+P_y+1equiv4pmod8.
]
The complete predecessor grammar forces its odd-a, depth-zero parent
[
R(t)=(2861931660t+767469219,;2092249530t+561067594).
]
Here (R) is odd/even and
[
R_x+R_yequiv6t+5pmod8.
]

For (t
otequiv3pmod4), this residue is respectively 5, 3, or 1 modulo eight, so the even-right inverse applies and forces
[
R'(t)=(4954181190t+1328536811,;1046124765t+280533796).
]
The exceptional case is (tequiv3pmod4), where (R_x+R_yequiv7pmod8) and the generic even-right uniqueness theorem does not apply.

Write (r=32+64j), as required by the root32 class. The exact root equation is
[
18018+211u+22155r=20cdot2^{E-13}.
]
After substituting (u=1802+6720t) and (r=32+64j), the Lean theorem `root32_tj_exact` proves the exact saturation identity
[
17300+22155(t+j)=5cdot2^{E-17}.
]
Since (Ege21), this implies
[
t+jequiv0pmod4.
]
Consequently the exceptional subcase (tequiv3pmod4) is exactly
[
jequiv1pmod4,qquad requiv96pmod{256}.
]
The Lean arithmetic certificate establishes these identities only; it does not itself import or re-prove the original source grammar.

## 4. R10592 composition draft and acceptance boundary

For (requiv10592pmod{16384}), the exact root-index equations give
[
j=(r-32)/64equiv165pmod{256},qquad
t+jequiv196pmod{256},
]
hence (tequiv31pmod{256}).

The intermediate file `Root32HighStopR10592Core.lean` attempts to close the D0E branch on this exact cylinder:
1. The complete even-even parent fan forces the displayed direct parents through (d_0,ldots,d_6), reaching (d_7).
2. The complete sum-zero parent theorem leaves (d_8) or E7(t); (d_8) is excluded by the even/odd four-step inverse followed by the source odd-image sum-two theorem.
3. E7(t) is forced to P(t), then to R(t) by the exact even/odd valuation-two inverse. With (t=31+256m), (q=(t-3)/4=7+64m), so the existing (R)-unreachable (qequiv7pmod{64}) theorem excludes it.
4. The corrected P7 theorem returns three residuals D0E, L, or P7E1E. The draft handles D0E by this chain, L by the existing LCore result, and P7E1E by the accepted `Root32HighStopA4Core.p7e1e_unreachable_of_t_mod32_31` theorem.

**Status:** the R10592 composition is still uncompiled and unaccepted. It was statically corrected to bind the root-derived (t) and the three-residual theorem's existential (t') through the shared (u=1802+6720t) equation. The current local runtime did not permit a Lean preflight; independent local RC2 preflight has been requested from Agent 24 and Agent 32. No CI run is being substituted. The file must compile from the exact current-main transitive source closure under Lean 4.36.0-rc2, then have its `#print axioms` output checked before any acceptance claim.

This composition addresses only the existing (requiv10592pmod{16384}) class. The earlier (requiv9568) and (requiv224) claims remain withdrawn; the full corrected nine-class union, including the A4 high-valuation parent families and the (tequiv1pmod{16}) branch, remains open.
