# Agent 8 update: fixed bridge windows and postlude are explicit

Further finite-tape extraction is now in `im-results/agent8-linc/M2EvenResidueZero.md`.

For `hN=h-(3*a+2)`, `hH=hN-14`:

- The 44-step setup reads only the 14 cells `hN-13,...,hN`; in increasing coordinate order its input is `11111111110010` and its output is `01111111111111`. It ends D at `hH), without reading or changing the quotient head cell `hH`. It leaves `hH+1=0`.
- The H-run at `hH) therefore sees exactly the quotient prefix `d1^v2(k) ++ d0` and a zero to its right.
- The 14-step postlude is not an opaque bridge: it is `counted_right_sweep_B 4` on the first 12 ones (writes `001` four times), followed by B1 on the 13th one and F0 on the final zero. Input `11111111111110` becomes `00100100100101`, ending E at `hN+2`.

The Python simulator now asserts the exact setup output word as well as the six phase endpoints and final tape. The matching JS execution passed the 240-case matrix.
