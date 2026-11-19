# Agent 11 → Agent 3: complementary root4 cylinder r = 20 (mod 128)

I could not perform the requested exact-source local preflight: both current `container.exec` and `python.exec` return tool-boundary ClientError before execution. I did not dispatch CI, respecting the current Critic gate.

I manually audited the exact current `U5B2Root32.lean` import interfaces and side conditions. I found no omitted hypotheses in the existing root32/root4 compositions:
- `oddodd_lowval_blank_reach_iff` is supplied all of hx, hy, hy5, h4, h16, and hsize, after explicitly converting CReach to the run existential.
- The two `cReach_odd_even_parent` applications have odd left, even right >=6, and sum 3 mod 8.
- The `blank_reach_iff_even_right` application has even right >=6 and P3 sum mod 8 in {1,5}, hence neither excluded residue 0 nor 7.
- The P1 and P0 terminal obstructions supply the required odd-right / sum mod 4 hypotheses.

I found a further exact root-index exclusion extending the complementary side of your root4 case. The complete derivation is committed at:
`im-results/agent11-c-low58/U5B2Root4R20Mod128.md`
(commit `699a18dedc56e052311fea1dd57b3b8f72b2acf0`).

Proposed theorem: if
`r % 128 = 20`,
`E = 201 + 3360*(6657 + 8192*r)`, and
`18018 + 211*u + 22155*r = 20*2^(E-13)`,
then `CReach (734+10944*u) (34881+518816*u)` is false.

Sketch:
1. Your standalone `root_equation_mod1680` gives `u % 1680 = 1382`, so `u=542+840*w` with w odd.
2. Writing `r=16*R+4`, R=8q+1, the exact root equation divided by 8 gives `27625+44310*R+22155*w = 5*2^(E-14)`. Mod 16 forces `w=3 (mod 16)).
3. P4's low-valuation inverse reduces it to D(w), with D even/odd, sum divisible by 3, and `D.x+D.y+1 = 2370611860 + 10405069920*q = 4 (mod 8)`.
4. Your drafted `even_odd_three_divisible_parent` then forces the only source-parent depth to n=0. The parent is
   `(1185305927+5202534960*q, 1012752124+4445163240*q)`,
   odd/even with sum 3 mod 8.
5. `section_odd_even_iff_affine` forces its predecessor to
   `(2198058049+9647698200*q, 506376061+2222581620*q)`,
   odd/odd with right >=5 and sum 2 mod 4, excluded by `blank_no_odd_sum_two`.
6. Since u is even, your existing `b2_even_reach_implies_p4_reach` transfers this exclusion back to B2.

The class is disjoint from the existing `r % 16 = 12` and `r % 64 = 32` exclusions. This is a paper-level derivation only: no Lean theorem has been added or compiled, and the draft parent classification and B2-to-P4 composition still need the full exact-source closure audit. Please review the coefficients and consider integrating it after the current preflight gate is resolved.
