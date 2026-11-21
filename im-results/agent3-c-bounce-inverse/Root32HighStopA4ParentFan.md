# Root32 P7E1E → A4: exact all-depth source-parent fan

**Intermediate mathematical result, not a nonreachability proof.** The P7E1E→A4 reduction and all-depth source-parent fan are paper-level. The t≡31 (mod32) A4 exclusion is separately Lean-accepted in `Root32HighStopA4Core.lean`; a generic P7E1E→A4 Lean draft exists in `Root32P7E1EGenericA4.lean` but is uncompiled. The q=1 A4 parent branch for t≡719 (mod1024) is now paper-level excluded; q=0 remains open.

## 1. Reduction to A4

For odd t with t ≡ 15 (mod 16), the corrected P7E1E residual is

```
P7E1E(t) = (1376399640*t + 369101882,
            2835015540*t + 760251268).
```

Its target coordinates are even-even and their sum is 2 (mod 8). The even-even parent fan therefore leaves only the direct parent

```
D(t) = (4211415180*t + 1129353148,
        1417507770*t + 380125633).
```

For this D(t), the exact congruence is

```
(D_x + D_y + 1) % 16 = 8.
```

The odd-seven inverse forces its parent to be

```
A4(t) = (2814461475*t + 754739388,
         (4231969245*t + 1134865019)/2).
```

Thus P7E1E(t) reachability implies A4(t) reachability. The formulas above are exact affine identities, not fitted numerical data.

## 2. A4 arithmetic

Put x=A4_x(t), y=A4_y(t), S=x+y. Direct expansion gives

```
S = (9860892195*t + 2644343795)/2
  = (5/2)*(1972178439*t + 528868759),

x + 2*y = 7046430720*t + 1889604407.
```

For odd t, the bracket in the factorization is even. Hence 5 divides S, and S>8 for every positive t in these root cylinders.

## 3. Exact source-parent fan

Consider a source transition from (a,k) to (x,y), with x,y odd and y≥5.

The complete section-preimage cases reduce as follows:

- The low branch is impossible because its output right coordinate is even.
- The a=1 high branch is impossible because it requires S+1 to be even, whereas S is even.
- The odd-a high branch is impossible for the same parity reason.
- The a=0 high branch requires S=8*2^m. This is impossible because 5 divides S and S>8.
- Only the even-a high-bounce branch remains.

In that branch, the cost equation and parity force the bounce depth n to be even. Write n=2q and U=a+2. The exact parent equations become

```
S = 2 * 4^q * U,
U >= 4,
U % 2 = 0,
a = U - 2,
2*k + U + 6*q = x + 2*y - 5,
2*k > a.
```

Conversely, any q,U,k satisfying these equations and inequalities gives the corresponding even-a source transition. Therefore this is an exact all-depth parent characterization, subject only to the stated source-region inequality.

The factor 5 now gives a useful constraint on every possible parent:

```
U % 5 = 0,
U % 2 = 0,
therefore U % 10 = 0 and a % 10 = 8.
```

Reducing the cost equation modulo 5 and using x+2y ≡ 2 (mod 5) gives

```
2*k + q ≡ 2 (mod 5),
therefore k ≡ 2*q + 1 (mod 5).
```

These congruences hold for every admissible depth, not just the shallow parents.

## 4. Depth ranges on the current root32 cylinders

The table uses the corrected S formula above. The v2 values are constant across each indicated cylinder except the last, where only a lower bound is uniform.

| t cylinder | v2(S) | possible q |
|---|---:|---|
| 31 mod 256 | 3 | 0 |
| 47 mod 256 | 4 | 0, 1 |
| 79 mod 512 | 5 | 0, 1 |
| 15 mod 512 | at least 8 | 0 through floor((v2(S)-2)/2) |
| 159 mod 1024 | 3 | 0 |
| 719 mod 1024 | 5 | 0, 1 (q=1 excluded below; q=0 remains) |
| 1167 mod 4096 | 6 | 0, 1, 2 |
| 7839 mod 8192 | 3 | 0 |

In particular, the A4 fan is finite with at most three candidate depths on seven of the eight cylinders. The t ≡ 15 (mod 512) family has a genuinely unbounded depth range as t varies.

Write t=719+1024s. For q=1, the exact affine formulas are
`U=S/8=443289114500+631097100480s`,
`a=U−2=443289114498+631097100480s`,
`k=(x+2y−U−11)/2=2312492088788+3292223978400s`.
Thus a≡2 (mod8), k≡4 (mod8). This is an even-even target with sum≡2 (mod4), so its complete parent fan forces
`D=(a+k−2,(k−2)/2)`.
Substitution gives
`D_x=2755781203284+3923321078880s`,
`D_y=1156246044393+1646111989200s`.
Hence D_x≡0 (mod4), D_y≡1 (mod4), and (D_x+D_y+1)≡2 (mod4), with D_x>5 and D_y≥5.

The complete `section_preimage_all_iff` grammar gives no source predecessor for any (X,Y) with X even, Y odd, Y≥5, X>5, and (X+Y+1)≡2 (mod4): zero-left/even-a branches require X+Y even; a=1/odd-a high branches require X+Y+1 divisible by four; the direct branch requires Y even; small branches contradict the size bounds. Thus D is unreachable and the q=1 branch is eliminated. This is a paper-level branch exclusion only; the q=0 branch remains open.

## 5. What this does and does not establish

Established algebraically:
1. P7E1E reachability reduces to A4 reachability on the relevant t ≡ 15 (mod 16) cylinders.
2. Every possible A4 source parent lies in the explicit even-bounce fan above.
3. Every such parent satisfies U ≡ 0 (mod 10) and k ≡ 2q+1 (mod 5).
4. The finite/infinite depth ranges in the table follow from exact 2-adic valuations; the t≡719 q=1 candidate is separately eliminated by the no-predecessor argument above.

Not established:
- The other A4 cylinders remain open. A separate, still-uncompiled source-proof draft now excludes A4(t) for t ≡ 31 (mod 32) using the existing odd/odd low-valuation inverse; it does not formalize the full all-depth fan.
- The exceptional parent states still require source-level exclusion. In particular, t≡719 q=0 remains open after the q=1 branch elimination.
- This file has not yet been compiled with Lean 4.36.0-rc2. The local Python/shell execution tools returned ClientError during this invocation, so no uncompiled claim is being promoted into results/.

The next useful step for the remaining t ≡ 15 (mod 32) cylinders is still to formalize the all-depth fan and attack the surviving parent family using the simultaneous mod-10/mod-5 constraints. Do not infer whole-cylinder exclusion from representative t values: deeper inverse steps can depend on higher bits of t.


## 6. Accepted low-valuation closure: t ≡ 31 (mod 32)

This cylinder is a special slice of A4 where the target sum has exact 2-adic valuation three:

```
(A4_x(t)+A4_y(t)) % 16 = 8.
```

It can be closed without formalizing the full all-depth fan. The standalone source-connected proof in `Root32HighStopA4Core.lean` applies the already source-certified `oddodd_lowval_blank_reach_iff`, forcing

```
p = (A4_x+A4_y-4)/2
q = (A4_x+3*A4_y-10)/4.
```

Exact affine arithmetic gives

```
8*(p+q) = 38046615075*t + 10202761387
8*q     = 18324830685*t + 4914073813.
```

For t ≡ 31 (mod 32), these imply q is odd and p+q ≡ 1 (mod 4). The existing `run_no_odd_sum_one` theorem therefore excludes the only parent, proving A4(t) unreachable on this cylinder.

The locally compiled core closes the corrected P7E1E residual there: its even/even parent fan has target sum 2 mod 8, so only the direct parent D(t) survives; `odd_seven_blank_reach_iff` then forces A4(t). The core was compiled with Lean 4.36.0-rc2 through 52 project modules, with all 51 imported project-source blobs matching current main; the audited theorems have no `sorryAx`.

Under the existing root-index congruence \(t+j\equiv3780\pmod{8192}\), this t-cylinder implies \(j\equiv5\pmod{32}\). Since \(r=32+64j\), the P7E1E residual exclusion therefore maps to \(r\equiv352\pmod{2048}\). This is a residual-specific index map only; it is not a complete high-stop exclusion.

**Acceptance boundary:** the P7E1E residual exclusion on t ≡ 31 (mod 32) is locally Lean-accepted in Root32HighStopA4Core.lean, with standard axioms only and no `sorryAx`. The generic t≡7 (mod8) reduction draft and the t≡719 q=1 branch exclusion are not Lean-accepted. This includes the t ≡ 31 (mod 256), t ≡ 159 (mod 1024), and t ≡ 7839 (mod 8192) cylinders. It does not close the other A4 cylinders, D0E, L, or the full high-stop target. Keep the dossier in im-results/; the full high-stop composition is not accepted.



## Secondary source-parent fans for the q=0 lift (t ≡ 719 and 79)

This goes one source edge deeper than the A4 parent fan above. It is an exact inverse-grammar reduction, but has **not** been Lean-compiled in this invocation. Write Reach(x,y) for true blank-origin section reachability.

### The t = 719 + 1024s family

The q=0 parent of A4 is
\[
T_0(s)=(X_0,Y_0)
\]
with
\[
X_0=1773156457998+2524388401920s,\qquad
Y_0=1647558417041+2345578327680s.
\]
Put \(H=X_0+Y_0+1\). Then
\[
H=3420714875040+4869966729600s,\qquad v_2(H)=5,
\]
since \(H\equiv32\pmod{64}\) for every \(s\).

For a source predecessor \((a,k)\) of \(T_0\), the exact section-preimage grammar leaves only the odd-\(a\), high-bounce branch. The zero-left branch and even-\(a\) high branch have even output sum, the low/direct branch has even right output, and the exceptional \(a=1\) branch would require \(H\) to be a pure power of two (whereas \(H/32\) is odd and greater than one). In the remaining branch, if \(n\) is the bounce exponent, then
\[
a=H/2^{n+1}-3,\qquad
k=(X_0+2Y_0-H/2^{n+1}-4-3n)/2.
\]
Because \(a\) is odd, \(a+3\) is even, so \(n\le3\). All four values \(n=0,1,2,3\) give valid positive source parents; there are no other parents.

| \(n\) | first coordinate \(a_n(s)\) | second coordinate \(k_n(s)\) | source-level disposition |
|---:|---|---|---|
| 0 | \(1710357437517+2434983364800s\) | \(1678957927278+2390280846240s\) | \(a\equiv5,\ k\equiv6\pmod8\), so \(a+k\equiv3\pmod8\); the exact six-even-right inverse forces the residual \(R_0(s)\) below |
| 1 | \(855178718757+1217491682400s\) | \(2106547286656+2999026687440s\) | \(a\equiv1\pmod4,\ k\equiv0\pmod8\); excluded by blank_section_no_one8 |
| 2 | \(427589359377+608745841200s\) | \(2320341966345+3303399608040s\) | both coordinates odd and \(a+k\equiv2\pmod4\); excluded by the original-source odd-right image theorem |
| 3 | \(213794679687+304372920600s\) | \(2427239306188+3455586068340s\) | \(a\equiv7\pmod8\), while \(k\equiv4+4s\pmod8\); for even \(s\) the six-even-right inverse reaches an odd-right sum-two state, but for odd \(s\) this parent has sum \(7\pmod8\) and remains open |

For \(n=0\), the six-even-right parent is
\[
R_0(s)=
(3389315364793+4825264211040s,\;
 839478963638+1195140423120s).
\]
It satisfies \(R_{0,x}\equiv1\pmod8\), \(R_{0,y}\equiv6\pmod8\), and
\[
(R_{0,x}+R_{0,y}+1)\equiv16+16s\pmod{32}.
\]
Consequently, for even \(s\), sumseven_forced_root_iff gives the exact next reduction to
\[
R_1(s)=
(4228794328429+6020404634160s,\;
 419739481818+597570211560s).
\]
Here \(R_{1,x}\equiv5\pmod8\), \(R_{1,y}\equiv2\pmod8\), and
\((R_{1,x}+R_{1,y}+1)\equiv8\pmod{16}\), so mod16_seven_blank_reach_iff gives its exact two-parent split. This split has not yet been closed. For odd \(s\), \(R_0\) has sum-plus-one \(0\pmod{32}\), outside the cited sum-seven root theorem.

Thus the exact secondary reduction is
\[
\operatorname{Reach}(T_0(s))
\iff
\operatorname{Reach}(R_0(s))
\ \lor\
\bigl(s\text{ odd}\ \land\operatorname{Reach}(P_3(s))\bigr),
\]
where \(P_3(s)\) is the \(n=3\) parent in the table. In particular, the q=0 lift is **not** excluded: the unresolved pieces are the \(R_0\) family and the odd-\(s\) \(P_3\) family. Do not promote this to results/.

### The t = 79 + 512s family

The q=0 parent of A4 is
\[
T_0(s)=
(195413706798+1262194200960s,\;
 181571962241+1172789163840s).
\]
For \(H=X_0+Y_0+1\),
\[
H=376985669040+2434983364800s,\qquad v_2(H)=4.
\]
The same exact source-grammar argument leaves precisely the three odd-\(a\), high-bounce parents \(n=0,1,2\):
\[
\begin{aligned}
P_0(s)&=(188492834517+1217491682400s,\;
          185032398378+1195140423120s),\\
P_1(s)&=(94246417257+608745841200s,\;
          232155607006+1499513343720s),\\
P_2(s)&=(47123208627+304372920600s,\;
          255717211320+1651699804020s).
\end{aligned}
\]
Their useful residues and existing source gates are:
- \(P_0\): \(x\equiv5,\ y\equiv2\pmod8\), \(x+y+1\equiv16s\pmod{32}\), and \((5x+9y)\equiv35+48s\pmod{128}\). The second_sumseven_forced_root_iff gate applies on \(s\equiv7\pmod8\).
- \(P_1\): \(x\equiv1,\ y\equiv6\pmod8\), \(x+y+1\equiv8+24s\pmod{32}\). The sumseven_forced_root_iff gate applies on \(s\equiv3\pmod4\).
- \(P_2\): \(x\equiv3\pmod8\), \(y\equiv4s\pmod8\), and \(x+y+1\equiv12+12s\pmod{32}\). The sum7_high_blank_unreachable gate applies on \(s\equiv1\pmod8\).

These are only subfamily reductions; the other parameter residues remain open. In particular, the t=79 q=0 lift is not excluded by this analysis.

### Verification status

The arithmetic above was recomputed with exact integer arithmetic and the source-preimage cases were reduced using the existing theorem statements. It has **not** been checked by Lean in this invocation. The local Python and container execution tools both return ClientError before command execution, so no local Lean acceptance or axiom audit is claimed. The next useful step is to formalize the t=719 q=0 secondary fan, then compose the existing sum-seven two-parent theorems against the residuals; do not add residue cylinders or claim a full A4 exclusion from these partial reductions.
