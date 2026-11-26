# Raw54 E1=0LE: four cold E0 siblings

All four child tables have form `1RB---_1RC---_0RD---_1LD0LE_<E0>0LE_------`. These are candidate ledgers, not closed Cover proofs. Frozen bank and enumerator are the same as the RF sibling.

| E0 | Split | Cycle | Last | Open | Max score found | Frozen FAR hits | Misses |
|---|---:|---:|---:|---:|---:|---:|---:|
|0LF|929|14910|5150|1308|812|1089|219|
|0RB|997|16539|4615|1778|390|1370|408|
|0RF|1837|31881|8377|1994|402|1645|349|
|1RA|2765|47151|14626|1819|985|1433|386|

Each census accounts for 9,765,625 complete tables. Max scores are lower bounds from observed halters only. `cold_census.py` regenerates each census and checks the exact frozen order against SHA256. Frozen bank Git blob: 56bf67275d597e354a0e827f6422ec68aa77f416.

## 0LF proof frontier

- `zeroLF-mut.txt`: 94 new one-edge FAR mutations (candidate witnesses).
- `zeroLF-ngram.txt`: 44 sparse n-gram candidates disjoint from the mutations. The generator regenerates the exact state and edge counts. At checkpoint, six of these (108,109,110,111,115,117) locally compiled with only propext, Classical.choice, Quot.sound.
- `Raw54ZeroLFGrowth13.lean`: three fully proved nonhalting partial machines, disjoint from the above. IDs are zero-based frozen FAR misses.

```
13 1RB1RC_1RC---_0RD0RA_1LD0LE_0LF0LE_0RA0RC
16 1RB0RC_1RC---_0RD1RA_1LD0LE_0LF0LE_0RA0RC
18 1RB---_1RC---_0RD1RF_1LD0LE_0LF0LE_0RA0RC
```

Common exact untrimmed zipper family A(n) has state A, left word 00, right word 00 followed by 4n+2 ones. Blank entry is 9 steps; each epoch takes 12n+34 steps and increments n. C transfers a pair of ones in 2 steps; D drains a 1010 block in 8 steps, appending four ones to the opposite tape. Entry and fixed end phases account for the remaining steps. The Lean proof quantifies over every n and every compatible completion, including both missing transitions in variant 18.

`epoch` and `never` compiled in Lean 4.36.0-rc2 against the original SweepPumping module in RF certified artifact 15143833177. Axioms: propext, Quot.sound. No sorryAx or native_decide.

78 0LF misses remain without a candidate certificate (219-94-44-3). The other candidate witnesses still require complete original-source integration; this document does not assert 0LF is closed. The RF sibling's accepted exact threshold 14389 is independent of this work.
