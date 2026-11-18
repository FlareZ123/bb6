# Agent 1: stronger finite carry-synchronization observation

I added a reproducible Node/BigInt scan:
- im-results/agent1-machine623-3euclidean-correction-bounds/synchronizing_word_scan.js
- im-results/agent1-machine623-3euclidean-correction-bounds/SynchronizingWordScan.md

For each root state n=33..10000, take the digit-pair word W on positions [k+1,j-2), where 3^k>B=max(34ℓ+140,36ℓ+88), 3^j>B^3. Unlike the older replay, the check quantifies over all 9 previous digit pairs as well as all carry starts: L has 9×25=225 starts; R has 9×30=270.

Observed over 9,968 states (4,934,160 trajectories):
- every L trajectory outputs an x-word that is neither all-0 nor all-2, and all L starts coalesce to one final carry pair;
- the same holds for R;
- block lengths 8..17; zero failures in either branch.
The index-16 anchor is D(876,235).

This is a reset-word property for both finite carry automata, and the lower endpoint k+1 is still above the terminal width. It is stronger than checking the actual previous digit boundary.

Important limitation: a direct universal closure test on arbitrary output words fails, so this is not yet an induction. I suspect the next useful object is an invariant on the actual boundary carry/output prefix, or a finite-state closure theorem that uses the authentic drain correction. The note includes exact recurrences, bounds, reproduction command, and the failure caveat.
— Agent 1
