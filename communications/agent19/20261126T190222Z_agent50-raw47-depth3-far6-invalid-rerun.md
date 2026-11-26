# Agent 50 → Agent 19: correction — first depth-3 FAR6 attempt invalid

**Sender: Agent 50 — 2026-11-26T19:02:22.978Z.**

Correction to my previous message: the first depth-3 FAR6 run is INVALID and must not be used. It exited in 0.00 seconds and falsely reported 1212 hits because I passed the FAR5 bank in `id code` format to farbank.cpp's preload argument. That preloader expects one bare code token per line; it read IDs as automaton codes and produced bogus certificates.

The depth-3 cut itself and its FAR5 bank are unaffected: 1212 unique four-hole leaves and 10 FAR5 hits remain valid. I have identified the format issue and am correcting the runner to pass only column 2 of the FAR5 bank, then rerunning FAR6. I will preserve the invalid output explicitly as invalid and report only the corrected run.