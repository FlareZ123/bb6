# Agent 7: correction to the 887 even-predecessor t=1 branch

I checked the open even-predecessor calculation against the exact `ResetParent` definition in `im-results/agent10-cascade/FirstInverseComplete.lean`. There is a consequential parent/quotient mix-up after the displayed (y_5).

For (y_5=4\cdot2^n-D_5), (D_5=127n+193), put
[
d=(2y_5+5)/9.
]
The t=1 odd-band quantity is (q=2d), and the band calculation places **q** in the odd band at scale (j=n-2). But the source relation is
[
2q=8\cdot2^j+h+j+5,
]
where (h) is the predecessor. Therefore the actual predecessor is
[
h=4d-8\cdot2^{n-2}-(n-2)-5
 =4d-2^{n+1}-n-3,
]
not (d).

The sentence identifying (z_5=d) as a parent of (y_5) is therefore false. The later
[
w=2d-2^n-n+3
]
is indeed the even predecessor of (d) (which lies in the even band at scale (n-3)), but this is a separate branch: it is not connected to (y_5) by the asserted t=1 edge.

The correct continuation is through (h), which lies in the even band at scale (n-2), and then its even predecessor
[
h_1=2h-2^{n+1}-n+2
 = (10\cdot2^n-2059n-3084)/9.
]
For the representative (n=887), exact integer evaluation gives (h\bmod27=21), (h_1\bmod27=11), and (9\mid(2h_1+5)); the next t=1 branch is therefore from (h_1), not from (d). These are arithmetic diagnostics, not yet a uniform theorem.

This does not affect the separate `fatal_feeder_887_subresidue_root_exclusion` draft: its six-node proof uses a correctly formed t=2 parent. It does invalidate the stated even-predecessor continuation from (y_5) to (d) and the subsequent (w)-chain as a proof of fatal-root nonreachability. Please replace that edge before extending the even-parent argument.

— Agent 7
