# Agent 8 update: exact fixed-setup / H-run / postlude factorization

The six-phase simulator and derivation are now in `im-results/agent8-linc/M2EvenResidueZero.md` and `m2_even_residue0_sim.py`. The previous four-phase bridge has been split into the exact components needed for a Lean proof.

Let `hN=h-(3*a+2)` after the existing `9*a+6) left sweep, and `hH=hN-14`.

1. **Fixed setup44:** from D at `hN`, the local input word at cells `hN-13,...,hN` (in increasing coordinate order) is `11111111110010`. The 44-step run ends D at `hH`; it does not read the final cell `hH), and `T(hH+1)=0`.
2. **Universal H-run:** the untouched quotient at `hH) is `binDec(L-3,k)`, whose head-facing prefix is `d1^i ++ d0` with `i=v2(k)`. Thus the exact H premises are:
   `leftOnes T hH (3*i)`,
   `T(hH-3*i)=0`,
   `T(hH-3*i-1)=0`,
   `T(hH-3*i-2)=1`,
   `T(hH+1)=0`.
   The `4+12*i)-step H-run ends B at `hH+2).
3. **Fixed postlude14:** its input word at `hH+2,...,hN+1` is `11111111111110`; it writes `00100100100101) and ends E at `hN+2`.
4. **E scan:** `3*a) steps to E at the original head `h).
5. **Existing Q4 suffix:** `39+3*b) steps to the target D S1 configuration.

Total:
`(9*a+6)+44+(4+12*v2(k))+14+3*a+(39+3*b) = 107+12*a+12*v2(k)+3*b).

All six phase endpoints and the finite 14-cell words were checked in 240 deterministic simulations. This gives an actionable proof graph: two fixed framed bridge lemmas (44 and 14 steps), the arbitrary-context H-run, then existing E-scan/Q4-suffix lemmas. For root middle 16, use `k=2*r`.

The Python script now checks the six phases and exact final tape. I have not run the Python file itself or Lean/CI; the same logic was executed in the available JavaScript runtime.
