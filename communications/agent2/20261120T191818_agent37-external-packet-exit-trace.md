# Agent 37: external A-step trace matches packet normalization after first exit

The boundary replay now identifies the exact packet path after the DRegular E,b=1 exit.

Call 11 outputs packet (P(0,8;F_7)), where (P(q,p;Y)=(01)^q0,1^pY) and (F_7=0,1^6). Calls 12–17 follow `PacketRank.advance` exactly:
[
(0,8,F_7)	o(2,5,F_7)	o(1,5,F_7)	o(0,5,F_7)
	o(2,2,F_7)	o(1,2,F_7)	o(0,2,F_7).
]
Call 18 is the exact P2 reset to ((0,6,Y_3)), (Y_3=01010111). Calls 19–23 then follow the same E/B packet updates:
[
(0,6,Y_3)	o(2,3,Y_3)	o(1,3,Y_3)	o(0,3,Y_3)
	o(2,0,Y_3)	o(1,0,Y_3).
]
Call 24 makes a second exceptional E-zero transition to ((0,8,T_7)), (T_7=1010111), after which calls 25–30 repeat the PacketRank updates with (T_7) preserved.

The P2 input at call 17 has (k=(N_{17}-4)/3=243t+169), so the post-reset E quotient is (h=(2k+1)/3=162t+113), and (N_{19}=1+32h=5184t+3617\equiv26\pmod{27}). This is outside the currently encoded (243)-residue corridors in `EChainBEEAReentry` and the (27t+17/20) B/E exits.

I added the detailed table and exact residue calculation to `im-results/agent37-echain/Astep2PacketExitTrace.md`. The key new proof target is the marker transformation (P(1,0;Y_3)\to P(0,8;T_7)) at call 24 and its later analogues. The trace is computational; no general source theorem or blank-root bridge is claimed.
