# Agent 1 → Agent 6: corrected finite filter explained by root rows

The corrected affine audit (see the correction immediately above) has a simple root-level explanation, so it need not be integrated as a large collection of `cert 14` evaluations.

For `d=M*q+r`, the pre-reset affine state is:
```
A = M*2^n + M/2
a = 2^n*(r+c) + (2*r-3*n-C)/4
B = M*(2^(n+1)-1)
b = 2*(a-r)+1
```
where `c,C=(10,25)` for branch 9 and `(6,21)` for branch 10. This corrected `a) was checked against derive.py's n=1,d=224 sample.

The 17 `cert 14` exclusions in the short list break down as follows:

1. **n=5, branch 9:** all 15 excluded residues have the prestate pair
   `a % 16 = 11`, `b % 8 = 3`. The existing `BB429NewRootRows.rooted_eleven` theorem requires the second residue to be in `{2,6,7}`; all 15 are ruled out immediately.
2. **n=13, branch 9, r=22:** same `(11 mod 16, 3 mod 8)` violation, so `rooted_eleven` rules it out.
3. **n=13, branch 9, r=6:** prestate `a=131059, b=262107`, hence `a % 16=3`, `b % 8=3`. The new compact lemma `odd_odd_mod4_three_sum` from my earlier message applies: for a genuine reachable odd/odd state with `a>=13` and `a%4=3`, the forced odd-back predecessor has positive even first counter, so positive-even-eight forces `(a+b)%8=2`. Here that would require `b%8=7`, contradiction.

So the useful finite reduction is exactly:
- n=5: 44 → 29 d residues;
- n=13: 4 → 2 d residues (6 and 22 removed);
- other n<18 rows unchanged by these root rows.

This gives a short source-level proof path: transport the genuine source prestate to `Reach`, apply `rooted_eleven` or `odd_odd_mod4_three_sum`, and use the explicit branch formula. The affine cert computation is a cross-check, not needed for these 17 exclusions.
