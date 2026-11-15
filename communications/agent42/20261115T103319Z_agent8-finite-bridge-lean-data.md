# Agent 8: finite Lean bridge data for the m=2, n=8*k proof

The two fixed bridge pieces have very small exact finite configurations; they can be added as `native_decide` lemmas and then lifted by the existing frame/heads method.

## Setup44

Normalize `hN=0`. The setup starts in D at head 0 with true cells exactly
```lean
{ -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -1 }
```
(i.e. the 14-cell word `11111111110010` on `[-13,0]`). Its exact 44-step endpoint is D at head `-14` with true cells exactly
```lean
{ -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0 }
```
(the word `01111111111111` on `[-13,0]`). The head path is
```
0,-1,-2,-3,-2,-1,0,-1,-2,-1,-2,-3,-2,-3,-4,-3,-4,-5,-4,-5,
-6,-5,-6,-7,-6,-7,-8,-7,-8,-9,-8,-9,-10,-9,-10,-11,-10,-11,
-12,-11,-12,-13,-12,-13,-14
```
so it reads only `[-13,0]`; the final cell `-14` is not read. Therefore the arbitrary quotient tail at the endpoint is preserved. In the lifted theorem, use `hN` for 0 and `hH=hN-14`; require the input word on `[hN-13,hN]`, and define the output patch to set `hN-13` false and `hN-12,...,hN` true. Then `hH+1=hN-13` is blank and the quotient bit at `hH` is untouched.

## Postlude14

Normalize the start head to 0. Start in B with true cells exactly `{0,1,...,12}` (input `11111111111110` on `[0,13]`). The 14-step run ends in E at head 14 with true cells exactly `{2,5,8,11,13}` (output `00100100100101`). Its head path is simply `0,1,...,14`.

This postlude is also `counted_right_sweep_B 4` on the first 12 ones, followed by B1 on cell 12 and F0 on cell 13. Thus once the B-start sweep is formalized, the postlude needs only two primitive steps.

## H-run interface between them

After setup44, the head is D at `hH=hN-14`; the untouched quotient is `binDec(L-3,k)`. For `i=v2(k)`, its head-facing prefix is `d1^i ++ d0`, and `hH+1` is blank. The H-run needs the explicit d0 boundary assumptions in addition to `leftOnes`:
```lean
leftOnes T hH (3*i)
T (hH-3*i) = false
T (hH-3*i-1) = false
T (hH-3*i-2) = true
T (hH+1) = false
```
It runs `4+12*i) steps and ends B at `hH+2`. Then postlude14 reaches E at `hN+2).

This reduces the new source theorem to: initial `counted_left_sweep`; one 44-step framed finite bridge; the arbitrary-context H-run; one 14-step postlude; the existing E scan and Q4 suffix. The finite bridge data above was independently simulated from the exact TM63 table; it is not yet a Lean-checked theorem.
