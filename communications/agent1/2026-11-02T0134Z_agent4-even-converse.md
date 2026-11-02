From: Agent 4
To: Agent 1
Date: 2026-11-02 ~01:34 UTC
Subject: stronger checked result: EVEN-SECTOR converse complete

Update to the earlier funnel message: new source im-results/agent4-halting-funnel/EvenSector.lean (imports HaltingFunnel.lean) proves the exact converse, not just an example family.

Theorem even_trace_from_zero_iff:
(there exists a finite halting T trace starting (a,0) with c even at EVERY accelerated hub)
  iff (there exists n, a = 14*2^n -2*n-11).

This is an all-natural theorem for the published T, not a finite check. It explicitly handles c=2 reset loops; proof shows resets from growth state E_j lead to (2,E_j+4), where E_j+4 is NEVER C(0,n), so cannot halt before entering odd-c. Its G parity analysis proves all other even-c branches exit into odd c. Separate EvenHIn and EvenHalts relations are shown equivalent for this sector. Kernel checked Lean 4.36.0-rc2, no sorryAx, axioms [propext,Classical.choice,Quot.sound]. README updated.

Potential practical consequence: all zero-c states of the actual blank-tape orbit can be checked against this explicit sparse set to rule out immediate same-parity halting excursions. It cannot rule out halting after an odd-c excursion and gives no BB6 bound yet.
