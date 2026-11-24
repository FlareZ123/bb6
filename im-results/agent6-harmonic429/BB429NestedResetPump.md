# Nested reset pump after the \(F^{26}E_{\rm odd}\) phase

**Status:** reproducible finite-orbit result. It is not an infinite-run proof or a BB(6) result.

This report continues from the exact endpoint \((0,805306356)\) established by [BB429RootResetPump.md](BB429RootResetPump.md), reached from the blank root at step 234,457,579.

## Exact branch word

Starting from \((0,805306356)\), the checked path is
\[
F^{27}\,O_{\rm even}\,E_{\rm even}\,
(F^{24}E_{\rm even})^{1458887}\,
F^{25}\,O_{\rm odd}\,E_{\rm odd},
\]
and it returns to \((0,939524164)\) after 36,472,231 transitions.

The outer prefix is:
\[
(0,805306356)\xrightarrow{F^{27}}(402653181,75)
\xrightarrow{O_{\rm even}}(402653151,146)
\xrightarrow{E_{\rm even}}(11,805306446).
\]

For a state \((11,V)\), 24 consecutive F steps give
\[
(234881021,\;V-469761948).
\]
When \(805306446\le V\le939523958\) and \(V\equiv2\pmod4\), the second coordinate is even, the gap is even and at least 16, and the next branch is \(E_{\rm even}\). Its update is
\[
(234881021,V-469761948)\xrightarrow{E_{\rm even}}(11,V+92).
\]
Thus the inner pump repeats 1,458,887 times, taking \(V\) from 805306446 to 939524050.

The final segment is:
\[
(11,939524050)\xrightarrow{F^{25}}(469762045,57)
\xrightarrow{O_{\rm odd}}(469762020,114)
\xrightarrow{E_{\rm odd}}(0,939524164).
\]

The transition count is
\[
29+25\cdot1458887+27=36472231.
\]
Combined with the preceding blank-root certificate, this reaches \((0,939524164)\) at step 270,929,810.

## Reproduction

    g++ -O3 -std=c++17 BB429NestedResetPump.cpp -o /tmp/bb429-nested-pump
    /tmp/bb429-nested-pump

Expected output:

    start: (0,805306356)
    outer: F^27 Oeven Eeven -> (11,805306446)
    inner: 1458887 x (F^24 Eeven), V += 92 -> (11,939524050)
    final: F^25 Oodd Eodd -> (0,939524164)
    total transitions: 36472231

The C++ program checks every branch in the outer prefix, all 1,458,887 inner cycles, and the final suffix. It is a finite computational certificate; it does not establish that the subsequent root trajectory is infinite.
