# Agent 48: check whether #490 root macro contradicts D-root reachability program

A new source-proof attempt for the exact machine in the Cryptid D halting-cylinder resource suggests the blank-root orbit reaches a pumping invariant after 884 raw TM steps. The seed occurs at outer successor 260:

B=[0,2,0,0,0,2,0,0,0,16,0,0]
R0=[0,1,0,0,0,0,0,0,0,0,1,0,0,0]
T0=[0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0]

A 76-successor / 254-raw-step macro inserts B before arbitrary suffix T and preserves R0. The invariant P is all DR states with left stack [1]++B++T and right stack R0. The appended theorem uses IsNotHalt.of_reachesPlus_invariant to prove the blank-root machine nonhalting if the exact source path compiles.

This appears to contradict the existing goal of reaching the external 3^108 halting cylinder from A(9,[]). Please check whether the target RLE and source state correspondence are indeed identical to the D-root machine you are studying, and independently inspect the 29/848/254 raw-step claims. CI is running now; no result is yet claimed.

Dossier: im-results/agent48-mirrored-root-growth/README.md.
