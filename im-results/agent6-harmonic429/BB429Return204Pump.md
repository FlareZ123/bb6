# A 657,930-cycle \(W\mapsto W+204\) reset pump

**Status:** exact finite first-return segment, checked by a C++ reproducer. Not an infinite-run or nonhalting proof.

This continues from \((0,939524164)\), reached at blank-root step 270,929,810 by the preceding reset-pump certificates.

## Macro

For the actual starting state, and throughout the verified parameter interval, the first-return word is
\[
F^{27}O_{\rm even}E_{\rm even}F^{25}O_{\rm odd}E_{\rm odd},
\]
which returns
\[
(0,W)\longmapsto(0,W+204)
\]
in 56 transitions.

The intermediate states can be expressed in terms of W:
- \(F^{27}\) gives \((402653181,W-805306281)\);
- \(O_{\rm even}E_{\rm even}\) gives \((11,W+90)\);
- \(F^{25}\) gives \((469762045,W-939523903)\);
- \(O_{\rm odd}E_{\rm odd}\) returns \((0,W+204)\).

The checked starting values are
\[
W=939524164+204i,\quad 0\le i<657930.
\]
They satisfy \(W\equiv124\pmod{204}\), hence \(W\equiv0\pmod4\), and range from 939524164 through 1073741680. The Eeven gap condition after the first two gap transitions remains valid through the last start; at the next W value, 1073741884, that phase condition fails and this macro no longer applies.

## Finite segment

The reproducer verifies all 657,930 cycles, including each F transition and each gap/reset transition. The total is
\[
657930\cdot56=36844080
\]
transitions, ending at \((0,1073741884)\). Combined with the previous certificates, this places the blank-root orbit at that state at step 307,773,890.

## Reproduction

    g++ -O3 -std=c++17 BB429Return204Pump.cpp -o /tmp/bb429-return204
    /tmp/bb429-return204

Expected output:

    verified 657930 cycles of F^27 Oeven Eeven F^25 Oodd Eodd, 56 steps each, W += 204
    final: (0,1073741884) after 36844080 transitions from (0,939524164)

This is still finite computational evidence. The subsequent phase from \((0,1073741884)\) is not classified here.
