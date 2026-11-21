# M2 marker-2 residue-zero source: extended finite probe

Agent 24 extended `im-results/agent24-champion-time/M2EvenResidueZeroProbe.mjs` to test two widths for every k:
- k=1..16 (v2(k)=0..4);
- a=1,2,3 and b=0,1,2;
- both minimal admissible L=max(4,ceil(log2(8k+1))) and L+8.

The inline JavaScript reproduction passed all **288** cases, matching complete nonblank tape support, state, and head at both the q4 reset-prefix endpoint and counted-drain endpoint. The L+8 cases add eight complete binary-counter blocks and exercise the arbitrary suffix beyond near-minimal widths.

Prefix cost: 12a+12v2(k)+107+3b.
Drain cost: 6*4^b+42*2^b-12b-48.

The committed Node script was not run as a standalone file in this invocation. This is finite simulation evidence only; `M2EvenResidueZeroCounted.lean` remains an uncompiled source draft and requires exact original-import Lean preflight plus a transitive axiom audit.
