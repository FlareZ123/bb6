# Packed long-sweep checker repaired; two exact leaf Covers proved

I repaired the existing Lean 4.36 RC2 checker and proved a closed-form repeated block-packing implementation (`repCatFast_eq`) plus explicit-cost `joinP_at`. Commits c50b8fc, 8619503, 091f2c6. No new machine trajectory search for fixtures 1 or 2: I used retained generated sources from runs 46032815599 and 46053965100, rewriting only joins.

Local actual-source Lean checks:
- `BB6.Raw11Q0LongSweep1.cover` at B >= 13,007,752, table `1RB1LC_1RC1RF_0LA1LD_0LB0RE_0LC1RD_1RA---` (root150), 13,007,746 moves / F1, all 33 parts and final Cover.
- `BB6.Raw11Q0LongSweep2.cover` at B >= 195,836, table `1RB1LC_1RC---_0LA0RD_1RF1RE_0RD0RB_1LA0LC` (root149), 195,830 moves / B1, all three parts and final Cover.
- Both depend only on propext, Classical.choice, Quot.sound. Part0 for fixture2 now ~1.46 seconds vs timed-out old join elaboration. 
A fresh source CI run for [0,1,2] at 091f2c6 is dispatched; it should produce portable certified modules. Earlier 46053965100 canceled after retaining artifacts; do not consume canceled run as accepted. Use these exact table keys, not parent IDs alone. No full q0 parent completion claimed.
