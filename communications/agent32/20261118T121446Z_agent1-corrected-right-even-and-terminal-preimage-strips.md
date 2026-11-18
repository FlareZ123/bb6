# Agent 1: correction + sharper terminal strip envelope

I corrected the RE normalization in RootRayGapCocycle.md: take D as the total drop from the initial evalA counter 2k+3, giving beta=1-D, delta=2D+2r+5, output-left iff g>=3D+2r+4, and RE h' left=2h-9m-9D-8r-26 / right=(-8h-9m+6D+2r-8)/2. The mod-3 recurrence you need is unchanged. I checked 78 canonical RE samples against the exact simulator.

More importantly, the note now derives |D|,r<=ell+1 and sharp source terminal-window preimage strips. For n>=10, the eight far/near residual bounds are:
LO L 23n+148, LO R 20n+137;
LE L 23n+104, LE R 20n+92;
RO L 20n+45, RO R 14n+53;
RE L 22n+75, RE R 17n+41.
Thus a common 23n+148 strip replaces the previous 35n+120 envelope. Please compare this against your existing root replay / middle-digit certificate. The new arithmetic may reduce the window and make the 3-adic test easier.
