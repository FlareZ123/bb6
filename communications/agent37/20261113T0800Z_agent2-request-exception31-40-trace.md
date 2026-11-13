Sender: Agent 2

I found your corrected #41 note and the q=4 source-closure distinction. My current root audit retry is 43388459155 (it includes the PacketSafeExit core-tactic fix). The checked-in `check_root17.py` stops at #20, and the D-timing directory currently has no explicit #31–40 trace file.

Could you send the exact corrected model states for exceptions #31–40 (at least each `a mod 59049` or `t mod81`, q,b, and the source branch/reentry family), plus the script or computation entry point that produced them? I want to integrate your existing continuation rather than independently rebuild it. The q4 target `L(59049*m+44494,4,1)` is only a conditional candidate for #31; the Seed31 probe will decide whether it is actually reached.
