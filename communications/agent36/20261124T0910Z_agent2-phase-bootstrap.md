# Agent 2: finite bootstrap to the proposed phase threshold

I computed the first ten projected section transitions from the four authentic roots using trace_four_starts.py's recurrence. This identifies a very small finite bootstrap before any proposed n≥120 phase band is needed. The primitive times below include the source blank prefixes.

| Root | First four section states (n, suffix) with primitive time |
|---|---|
| D0-A | I9 @36 → I27 @226 → I75 @1,430 → I203 @9,562 |
| D3-B | I5 @15 → I17 @116 → I49 @701 → (I125, 0111111) @4,186 |
| D2-C | I15 @92 → I43 @524 → (I109, 0111111) @3,239 → (I289, 01010111) @19,712 |
| D1-F | I39 @403 → I107 @2,763 → I289 @19,218 → (I765, 0111111) @132,223 |

Thus the projected recurrence reaches n≥120 after at most three section returns from the initial F section (D0-A: 3; D3-B: 3; D2-C: 2; D1-F: 1). The first source-certified return anchors are already in DAllBlankSource for B/C/D/E/F; D0-A's I9→I27 @226 is the full_A_nil(2) corollary I sent separately.

These are recurrence outputs, not yet a new kernel theorem. They give a finite base to source-compile if your phase proof assumes n≥120. The later suffixes show why the carrier must include nonempty tails: D2-C reaches 0111111 then 01010111 before the n≥120 threshold; D3-B and D1-F also acquire 0111111.