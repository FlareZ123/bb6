# General offset return arithmetic and correction of the first #490 token excursion

**Status:** exact source-clause derivation and independent BigInt replays; not a kernel-checked authentic-root theorem. Source is the pinned DeepMind #85 acceleration module at `3647718b5df22e1a61462dec0376bd204526285a`. The DR seed at raw step 7 is the mirrored #490 start (the genuine #85 start is CR at raw step 11). Keep those seeds distinct.

## 1. Previously missed token counter

Write `S(x,r,p)=tok_DR([2,x] ++ 1^p ++ [0], [], 0^r ++ [1])`, with the source list argument ordering. The earlier fixed-four-ones family in Agent24's TokenResidual2Continuation.md is **not closed under its zero-remainder branch**. The latter consumes one of the pending ones. For p>0 the exact three branches are:

- x>=3: S(x,r,p) -> S(x-3,r+4,p), cost 6r+35.
- x=0: S(0,r,p+1) -> S(2r+7,3,p), cost 8r+77.
- x=1: S(1,r,p) -> CR(0^(r+p+5) ++ [1], [0]), cost 6r+33+2p.
- x=2: S(2,r,p) -> CR(0^(p+1) ++ [1] ++ 0^(r+3) ++ [1], [0]), cost 6r+38+2p.

For the first rule use r tok_DR_zero steps, tok_DR_1_nil_28, r+1 tok_EL_1 steps, tok_EL_add3. For x=0, after the first three clauses the token list is [0]++1^(p+1)++[0] and the left list is 0^(r+4)1. tok_EL_0_cons changes the first following one into 2 and consumes the zero; tok_CR_zero increments that 2 by 2(r+4); tok_CR_1_nil_33 resets left length to 3 without restoring the consumed one. tok_EL_add3 gives the stated new x. The cost and x recurrence from the old note were correct, but **p decreases**. The x=1,2 formulas follow the same three-clause prefix, then respectively the one sweep or tok_EL_2 and the one sweep, then tok_EL_exit_zero. In the x=2 branch CR-one-zero subsequently consumes one zero of the second block, leaving r+2 zeros, not r+3.

For p=0 and x=0 the trailing zero is consumed and the token list loses its sentinel: the next S-like state is tok_DR([2,2r+6], [], 0^3 1) with no terminal zero. It must be handled separately; it is not the old S family.

## 2. Total normalization for a singleton-two suffix

Use H(x,r,p,e) for tok_EL with left list 0^r 1, token list [x]++1^p followed by a terminal zero iff e=true, and a preserved ordinary right context W. On the initial r=3 family x>=15. Batch q=floor(x/3) cycles of x->x-3,r->r+4:

```
cost = 12 q^2 + (6r+23) q
r <- r+4q; x <- x mod 3
```

This follows from tok_EL_add3 (5), r tok_DR_zero (4r), tok_DR_1_nil_28 (28), and r+1 tok_EL_1 (2r+2). If x=0 and e=true, the CR normalization costs 2r+34. If p>0, the new H is (2r+2,3,p-1,true); if p=0 it is (2r+1,3,0,false). If e=false, no additional zero branch is taken. Thus the internal loop terminates: p decreases or e changes from true to false. For the initial x>=15, every updated x after a zero branch is >=15, so r>=7 on residual-2 exit. An unbounded number of primitive TM steps can be summarized by a finite, explicitly bounded number of arithmetic batches.

For W empty, the last residue leads to D_0(c;T)=CR([0],0^5[c]T):

| Residue | c | T | Extra raw cost |
|---|---:|---|---:|
| 0, no sentinel | 2r-3 | [] | 2r+54 |
| 1 | 2(r+p+1)-3 | [] | 2r+4p+58 |
| 2 | 2r-7 | [2p+5] | 2r+4p+64 |

If the terminal zero is present, tok_EL_exit_zero bumps W; for W nonempty let h=W[0]+1. Add h to c for residue 1, or to the first suffix entry for residue 2, and preserve W's remaining entries. The empty-token exit with nonempty W is not covered by this formula (implementation defers it to the source interpreter).

In particular the exact prefix from G(M,[1]++0^z++[2]++W)=CR([0],0^M[1]0^z[2]W), M>=5, to H(2M+5,3,z+2,true) costs 4M+79+6z. The initial eight-transition prefix gives EL(0^(M+2)1,[1]0^z[2]W). EL-positive, DL-zero and the z-zero sweep give EL(0^(z+1)1 0^(M+1)1,[2]W). EL-positive and DL-one enter tok_DR([2,0],W,0^(z+1)1 0^(M+1)1); the z+1 tok_DR_zero steps, tok_DR_succ, M+2 tok_CR_zero steps and tok_CR_1_nil_33 give H as specified.

## 3. Corrected first authentic #490 token excursion (conditional source arithmetic)

Prior arithmetic and both interpreters agree on D_0(26,524,315;[0,0,2]) at raw step 153,499,683,790,849. Reducing c by thirds leaves M=35,365,757 and remainder 1. In H notation:

| x before batch | q | r after batch | residue | p |
|---:|---:|---:|---:|---:|
| 70,731,519 | 23,577,173 | 94,308,695 | 0 | 4 |
| 188,617,392 | 62,872,464 | 251,489,859 | 0 | 3 |
| 502,979,720 | 167,659,906 | 670,639,627 | 2 | 2 |

Thus the endpoint is **D_0(1,341,279,247;[9])** at raw step **392,515,651,843,862,559**, not D_0(1,341,279,249;[13]). The correction to p and the subsequent CR-one-zero consumption explain both endpoint differences. Later suffix-[13] deductions based on this first token excursion cannot be claimed as the actual #490 trajectory.

The new continuation (raw times from blank, conditional on the source rule transcription) is:

| c | T | raw time |
|---:|---|---:|
| 1,341,279,247 | [9] | 392,515,651,843,862,559 |
| 3,576,744,667 | [0,0,6] | 2,791,222,372,148,762,352 |
| 9,537,985,787 | [0,0,0,0,3] | 19,848,692,333,528,818,097 |
| 25,434,628,780 | [0,0,0,3] | 141,146,256,421,739,780,298 |
| 67,825,676,755 | [0,0,0,0,0,0] | 1,003,706,711,874,695,788,512 |
| 180,868,471,351 | [17] | 7,137,469,949,709,248,558,349 |

## 4. General offset grammar

For G(M,T)=CR([0],0^M T), M>=5, a positive leading x>=3 reduces x by 3 and increases M by 4, at cost 6M+39. Batched q shifts cost 12q^2+(6M+27)q. Leading zeros are absorbed into M without a transition. Let T begin with residue 1 or 2 or be empty after reduction:

- empty -> D_0(2M+1;[]) at cost 4M+81.
- 2 followed by W -> D_0(2M+9+h; W') at cost 10M+136, where bump(W)=[h]W' (empty gives [0]).
- 1 followed by z zeros only -> D_0(2M-3;[2z+5]) at cost 4M+91+4z.
- 1 followed by z zeros then v>=3 and W -> D_0(2M+1;0^(z+2)[v-3]W), cost 4M+99+6z.
- 1 followed by z>=1 zeros then singleton 1 -> D_0(2M-3;[2z+1,5]), cost 4M+101+4z.
- 1 followed by z zeros then 2 and W -> the token normalizer in section 2, with its stated exceptions.

These are source-clause arithmetic consequences, not an unconditional nonhalting theorem. The singleton-one adjacency branch and some contexts require fallback, and there are known halting prepared cylinders.

## 5. Executable arithmetic

`return_arithmetic.js` implements these formulas and explicitly returns null for uncovered cases; `affine_stack_replay.js` is the independent RLE source-rule interpreter with guard-checked affine jumps. Both preserve the root identity. The direct formulas matched endpoints and exact raw costs in 14,122 finite cases (including two-entry tails), with 748 uncovered cases left to fallback. A preliminary 7-second full-cost run completed 35,999 return iterations for #85, with one fallback and 32,304-digit cumulative count; 37,140 for #490, with no fallbacks and 33,336-digit cumulative count. These are computational prefixes, **not certified BB(6) bounds**. No halting verdict or global bound claimed.
