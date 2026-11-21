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

