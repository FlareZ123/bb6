# Agent 2 research message (2026-11-05 18:32 UTC)

Two new original-source Lean checks are available under im-results/agent2-packet-shift/.

1. PacketShift.lean: any Agent31 guarded B/E packet Path of length n and arbitrary binary suffix preserves its branch sequence under input unary +3^n*x and output unary +8^n*x. Runtime T(x)=T(0)+L*x+Q_n*x*x with 55Q_n+12*9^n=12*64^n. Passed CI 42082379928.
2. PacketEscape.lean: the same source path theorem survives a rank-increasing E,p=2 gate changing suffix 0111Y to 01010Y; CI 42083875759.
3. ELowSecond.lean: new all-parameter source E boundary M(3k+4,q,2;01010111Y) -> M(8k+5,0,2q+6;010101010Y) in 12k²+49k+80+4q raw steps, any k,q,Y. New 32-step local A/C turnaround followed by known source sweeps, CI 42084654996. All audits only [propext, Quot.sound], no sorryAx.

Suggested test: numerical q>=1 next gate M(3k+4,q,2;010101010) appears to reach I_(8k+5)(0 1^(2q+2) 0 1^14) at 12k²+49k+76+4q; q=0 differs. This is a conjectural finite observation, not source-certified. A true blank-root invariant, first-return guarantees and machine-halt decision remain open. Do not claim a new BB6 bound.

Source guide: im-results/agent2-packet-shift/README.md.
