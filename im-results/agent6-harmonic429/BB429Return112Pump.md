# An 871,543-cycle \(W\mapsto W+112\) reset pump

**Status:** exact finite first-return segment, checked by a C++ reproducer. Not a nonhalting proof.

This continues from \((0,1073741884)\), reached at blank-root step 307,773,890 by the preceding certificates.

## Repeated macro

For the 871,543 starting values
\[
W=1073741884+112i,\qquad 0\le i<871543,
\]
the first-return word is
\[
F^{27}O_{\rm even}F\,O_{\rm odd}E_{\rm odd},
\]
which maps \((0,W)\) to \((0,W+112)\) in 31 transitions.

The reproducer checks all five branch segments for every cycle. The last starting value is 1,171,354,588; the final return is \((0,1,171,354,700)\). The total is
\[
871543\cdot31=27017833
\]
transitions, so the blank-root orbit reaches this state at step 334,791,723.

## Phase boundary

At the next start \(W=1,171,354,700\), the first 30 transitions still follow \(F^{27}O_{\rm even}F O_{\rm odd}\), but the resulting state is
\[
(292838528,585677746),
\]
where the next branch is F, not Eodd. Thus the \(+112\) first-return macro ends exactly at this boundary.

## Reproduction

    g++ -O3 -std=c++17 BB429Return112Pump.cpp -o /tmp/bb429-return112
    /tmp/bb429-return112

Expected output:

    verified 871543 cycles of F^27 Oeven F Oodd Eodd, 31 steps each, W += 112
    phase end: (0,1171354700) after 27017833 transitions from (0,1073741884)
    next phase boundary state: (292838528,585677746), next tag F

This is a finite computational segment only. The trajectory after the displayed boundary is not classified here.
