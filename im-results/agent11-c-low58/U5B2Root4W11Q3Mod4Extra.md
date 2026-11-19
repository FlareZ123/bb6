# U5 B2 root4: ten W11 q-mod-256 Q-branch reductions

**Status:** new conditional nonreachability derivation, 2026-11-19. The exact modular and affine arithmetic was checked, but the composed theorem has not been Lean-formalized or compiled. Keep in `im-results/`.

## Root-index cylinders for the Q branch only

Assume the exact residual root equation
[
E=201+3360(6657+8192r),\qquad
18018+211u+22155r=20\cdot2^{E-13}.
]
Then the B2 target is blank-unreachable whenever
[
r\bmod32768\in
\{11092,9044,8532,2900,340,27476,24916,20820,19284,16724\}.
]

These ten residues are all (84\pmod{256}), so they sit in the W11 odd-q sector from `U5B2Root4W11OddDirectParent.md).

## 1. Root equation fixes q modulo 256

As before, `root_equation_mod1680` gives (u=542+840w) with w odd. Put (r=16R+4), and write (w=16q+11). For (q=256m+c), the exact equation divided by eight and reduced modulo 4096 gives
[
27625+44310R+22155(16c+11)\equiv0\pmod{4096}.
]
After division by two,
[
\frac{27625+22155(16c+11)}2+22155R\equiv0\pmod{2048}.
]
The inverse of 22155 modulo 2048 is 291. The ten q-residues and corresponding root-index residues are:
| (c=q\bmod256) | (R\bmod2048) | (r\bmod32768) |
|---:|---:|---:|
| 11 | 693 | 11092 |
| 27 | 565 | 9044 |
| 31 | 533 | 8532 |
| 75 | 181 | 2900 |
| 95 | 21 | 340 |
| 139 | 1717 | 27476 |
| 159 | 1557 | 24916 |
| 191 | 1301 | 20820 |
| 203 | 1205 | 19284 |
| 223 | 1045 | 16724 |

All ten c are 3 modulo four, but that is not enough to reduce P(q) to Q(q). The source parent fan also permits the high odd-a bounce parent
\[
A(q)=(1755476785+2411924550q,\;
     4250882050+5840468445q),
\]
whose coordinate sum is 2 modulo four only when q=1 modulo four. Here every c is 11 or 15 modulo 16, so the existing blank_no_odd_sum_two exclusion does not apply. The following exact path therefore concerns only the direct parent
\[
Q(q)=
(7021907149+9647698200q,\;
 1617666871+2222581620q).
]
## 2. Exact source inverse path from Q(q)

For q=3 mod4, (Q_x+Q_y\equiv8\pmod{16}), so the source-certified odd/odd low-valuation iff reduces Q to
[
D2(s)=(22125206738+23740559640s,\;
       15205309233+16315443060s),
\qquad q=4s+3.
]
The ten q-residues split into two source-certified next-step gates:
- c=11,27,75,139,203 give `s ≡ 2 (mod 4)`, hence ((D2_x+D2_y+1)\bmod8=4). Apply `evenodd_four_blank_reach_iff`.
- c=31,95,159,191,223 give `s ≡ 3 (mod 4)`, hence ((D2_x+D2_y+1)\bmod16=8). Apply `odd_seven_blank_reach_iff`.

After that exact step, the existing four-sector `blank_reach_iff_fullForcedNormalize` applies. The gate paths below list the complete chain from Q:
- O = `oddodd_lowval_blank_reach_iff`;
- F = `evenodd_four_blank_reach_iff`;
- S = `odd_seven_blank_reach_iff`;
- R = `six_even_right_blank_reach_iff`;
- A = `BB6.Agent15.blank_reach_iff_affine`.

| c | r mod 32768 | path | final normalized x(m) | final normalized y(m) | sum mod 4 |
|---:|---:|:---:|---:|---:|---:|
| 11 | 11092 | OFO | 55999994348 + 1222391153760m | 54639361181 + 1192690687440m | 1 |
| 27 | 9044 | OFORR | 326173235172 + 3011427184920m | 32295632285 + 298172671860m | 1 |
| 31 | 8532 | OSRA | 375067275991 + 3026277418080m | 36034334759 + 290747555280m | 2 |
| 75 | 2900 | OFO | 361597782788 + 1222391153760m | 352812033041 + 1192690687440m | 1 |
| 95 | 340 | OSRA | 1131636630511 + 3026277418080m | 108721223579 + 290747555280m | 2 |
| 139 | 27476 | OFO | 667195571228 + 1222391153760m | 650984704901 + 1192690687440m | 1 |
| 159 | 24916 | OSRA | 1888205985031 + 3026277418080m | 181408112399 + 290747555280m | 2 |
| 191 | 20820 | OSRAO | 1242121109548 + 1658512486680m | 729936333177 + 974630020980m | 1 |
| 203 | 19284 | OFO | 972793359668 + 1222391153760m | 949157376761 + 1192690687440m | 1 |
| 223 | 16724 | OSRA | 2644775339551 + 3026277418080m | 254095001219 + 290747555280m | 2 |

In every row the final right coordinate is odd and at least five, and the sum is 1 or 2 modulo four. The source-certified fullForcedExcluded_sound filter excludes the final normalized state, so this chain excludes Q(q). It does **not** exclude P(q), P4, or the original B2 target until the alternate parent A(q) is also ruled out. For these ten c classes, q is 11 or 15 modulo 16; that alternate-parent problem remains open. Do not count these rows as root-index exclusions.

## Validation boundary

The component inverse theorems and the four-sector normalizer/filter have original-source CI evidence. The new ten-case residue mapping and composed path table are not Lean-compiled. The W11 parent reduction and the D-parent/B2-to-P4 implications remain in the uncompiled `U5B2Root32.lean` closure. No CI was dispatched because the current Critic gate requires exact-source local preflight first.
