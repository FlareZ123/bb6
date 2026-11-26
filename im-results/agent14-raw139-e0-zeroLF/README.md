# Raw139 E0=0LF — exhaustive candidate partition and first exact holdout decision

Exact parent `[7,24,11,24,14,24,24,16,20,11,24,24]` (normalized row (2,0LF)). All six state labels are already introduced. This work is an intermediate candidate partition for the one parent, not a certified parent Cover or global BB(6) bound.

## Current classification

An ordinary 24-way first-hole census with move code order 0..23, raw replay cutoff 450, translated side-cycle period cap 120, and ordinary FAR dimensions 1/2 produced **27,887 splits and 641,402 terminal ordinary leaves**. The counts are:

| Kind | Leaves |
|---|---:|
| Translated cycle | 425,251 |
| Last undefined transition | 156,031 |
| Ordinary FAR | 47,474 |
| Initially open | 12,646 |

The initial open-list text SHA-256 is `f8c4e5d966547e2929994d1fc685a12b1e49bfb800eb2092ae3b3b9a5e463996`. A first pass of existing width-two/three block-FAR recipes and exact replay closed 12,226 block cases and 142 last-hole cases, leaving 273 unresolved and five late multi-hole queries. Expanding all 24 ordinary moves of each late query gives 393 additional search tasks (273+120), and the total expanded census has 27,892 splits / 641,517 ordinary leaves. Stronger translated-cycle replay (cutoff 4000, period cap 600) and ordinary FAR up to dimension three closed 135 cycle, 95 FAR and 7 last-hole cases. A second block-FAR search closed 145 of the remaining 156; 139 of these use reflection. Eleven one-hole tables remained, all of which ran beyond 10^9 raw moves in an exact width-12 block macro replay. The largest observed last-hole query among the classified cases was 19,001 (candidate weighted bound 19,007 for the covered leaves only).

**Residual 2040 is now mathematically decided.** [First-exit proof](Residual2040.md) proves nonhalting for all 25 completions of its single hole. It derives an unbounded orbit of sections with run/tail lengths (4k+1,2), (4k+2,3). This is an exact mathematical proof, not a long-run inference. Source Lean acceptance and parent assembly remain open.

The other ten one-hole tables are the remaining decision targets:

| ID | Exact table (4q+2w+r, 24=hole) |
|---:|---|
|1307|7,13,11,17,14,21,24,16,20,11,1,2|
|3002|7,23,11,13,14,1,24,16,20,11,3,6|
|3862|7,10,11,19,14,17,24,16,20,11,3,0|
|3863|7,10,11,21,14,17,24,16,20,11,3,0|
|3864|7,10,11,22,14,17,24,16,20,11,3,0|
|4125|7,9,11,24,14,21,2,16,20,11,3,0|
|4344|7,12,11,24,14,21,23,16,20,11,3,13|
|9015|7,21,11,24,14,3,0,16,20,11,14,17|
|10338|7,21,11,1,14,24,3,16,20,11,15,20|
|11287|7,8,11,3,14,21,24,16,20,11,19,2|

The census is a witness discovery experiment. A complete source certificate must replay every branch, including the omitted halting branch at each split; the above counts are ordinary leaves only. Do not infer nonhalting from the billion-step replay or a global roster reduction from any of these local results. Discovery source and exact manifest reconstruction are being consolidated in this dossier.

## Reproduction

Run `python /path/to/repo/im-results/agent14-raw139-e0-zeroLF/discover.py 4` in a scratch directory with g++ and Python 3. The script reconstructs the two-stage search using the existing Agent48 blockcert generator, compiling census.cpp in normal and EXTENDED modes. The original experiment ran independent batches in parallel; the consolidated script sorts IDs and runs the extended scan in one process. Its combined source is a reconstruction, not yet rerun end to end. Intermediate artifacts are candidate witnesses and require source certification. `long.cpp` independently supports exact finite block-macro replay: compile with `g++ -O3 -std=c++17 long.cpp -o long`, feed lines of residual ID followed by the 12 transition codes separated by spaces, and specify the desired primitive-step limit as the first argument. An open result is not a nonhalting certificate.

## Additional closures (14:27 UTC)

Three exact translated side-cycle witnesses were obtained by extending the search to outward edge configurations (not just the initial 4000-step/600-period window). Independent finite replay verifies the matching retained half-tape, state, displacement, and window:

| Residual | Entry | Period | Direction | Boundary | Displacement |
|---:|---:|---:|---|---:|---:|
|3864|1443|672|left|-2|-12|
|4344|5234|1112|left|-8|-8|
|11287|2656|948|right|-7|10|

The additional [10338 proof](Residual10338.md) establishes universal nonhalting by the exact odd-run recurrence. Its initial section is F at -98, ones -95..27, at step 6120. The remaining six mathematical holdouts are 1307, 3002, 3862, 3863, 4125, 9015. Lean modules are candidates pending original-source audit; replay.py verifies the three side-cycle witnesses and the 10338 initial section independently.

## Source acceptance and new witness (14:30 UTC)

Run [45839040551](https://github.com/FlareZ123/bb6/actions/runs/45839040551), pinned source `a2979f2be1130a3111af48ac62bdfad90c65c07d`, accepted the three side cycles and 10338 exact growth. Artifact 15126193553, digest `d2a84a66d1a3f9e993538e000345fd3692847698328cf364bf9d591d96fccb69`. Audit output shows only propext/Quot.sound for 10338; side cycles additionally use Classical.choice. These four exact original tables have certified universal nonhalting. Residual 2040 now has a candidate source formalization using simultaneous first-exit induction for the two relevant residues, awaiting compile. A width-four block-FAR candidate was found for 9015 using (width, cap, modulus, runs, reflect, phase)=(4,1,2,3,false,false), 99 left states / 255 right nodes. The generator `emit9015.py` uses the established source bridge. Neither new candidate is claimed source-accepted yet.
