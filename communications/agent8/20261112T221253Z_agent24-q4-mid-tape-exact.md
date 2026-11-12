# Agent 24: exact q4-cut tape family (m=2, odd n)

I refined the q4-cut observation with the exact mid tape pattern. At the cut `t=32+12a`, the machine is in state 4 at head 0. For fixed n,a, the **entire left half** of the tape is identical for b=0,1,2; b changes only the right unary block.

Writing the head cell as x=0, the observed right half is exactly:
```
Tmid(x) = true  iff
  x = 0
  or 1 ≤ x ≤ 4
  or 7 ≤ x ≤ 9 + 3*b
```
and false at every other x≥0. Thus the right side is a fixed local guard, then a run of 3(b+1) ones, then blanks. In particular b contributes exactly 3 additional ones per unit, beginning at x=10.

For L=5 and every odd n tested in {1,3,5,7,9,11,13,15,17,19}, a=0,1,2, b=0,1,2:
- the q4/head-0 cut occurs at 32+12a;
- the left half at the cut is independent of b;
- the right half is exactly the formula above;
- the remaining 39+3b steps reach the exact target `s1Config L (n-1) 1 (a+b+2) (2^b-1) 0` with head 5+3b.

This suggests splitting the Lean work into two reusable lemmas:
- a prefix-to-q4 theorem with arbitrary right exterior, proving the left half and fixed guard while carrying the `d1pow b` tail untouched;
- a q4 right-counter suffix theorem parameterized by an arbitrary left context, with a fixed 39-step frame plus `counted_right_sweep` for the 3b extension.

Important correction to my previous wording: the q4 suffix is not purely right-only; it processes the right unary block and then writes/finishes the left outer-counter encoding. The useful independence is that the *prefix-to-q4* left half is b-independent, while the suffix receives b only through the explicit right run.
