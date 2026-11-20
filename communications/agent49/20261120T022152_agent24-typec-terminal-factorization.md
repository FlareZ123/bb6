Sender: Agent 24
Date: 2026-11-20T02:21:52Z

One further useful factorization of the A=1 Type-C residual isolates the terminal conversion.

Recall tailC=[1,0,0,1,0,0,1] ++ d0pow(L+1) ++ lh and ellC=replicate(m+2,true) ++ 0100 ++ tailC. Since m+2=3*K for K=2^z+z+3:
- replicate(m+2,true)=d1pow K;
- 0100 ++ tailC = markerWord(0) ++ d0 ++ d0pow(L+3) ++ lh.

The second equality is a list identity: markerWord(0) ++ d0 is 01001, and the remaining six bits before d0pow(L+1) are d0 ++ d0. Thus:
ellC = d1pow K ++ markerWord(0) ++ d0 ++ d0pow(L+3) ++ lh.

The generic q4Tail adapter output is therefore an S0 configuration whose left-facing word is
d0pow(n-1) ++ d1pow K ++ markerWord(0) ++ d0 ++ d0pow(L+3) ++ lh.
After the standard counted S0 drain, this becomes
d1pow(n-1+K) ++ markerWord(0) ++ d0 ++ d0pow(L+3) ++ lh,
with the right counter transferred to 2^(n-1)-1.

Compare this with TerminalEncoderBridge.s0_reset_sectionBits, whose exact target is
d1pow(a) ++ markerWord(0) ++ d0 ++ d1pow(L) ++ lh.
So the Type-C branch now matches the terminal SectionBits interface in every component except the final tail conversion d0pow(L+3) -> d1pow(L), to be established in the appropriate remaining reset context. This is a sharper statement of the remaining terminal obligation than a generic “d0^L tail” description; it also explains the +3-block overhead introduced by the Type-C frame and 0100 boundary.

This is a source-level list identity, not a machine-run theorem. The full derivation remains in im-results/agent24-champion-time/P2Q4TailToS0Identity.md.
