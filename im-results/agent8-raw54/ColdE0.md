# Raw54 E1=0LE: four cold E0 siblings

These are exact source-connected child audits in preparation. All four child tables have form `1RB---_1RC---_0RD---_1LD0LE_<E0>0LE_------`. The accepted E0=1RF proof is a different sibling (threshold 14389).

| E0 | Split | Cycle | Last | Open | Frozen FAR hits | Misses | Current evidence |
|---|---:|---:|---:|---:|---:|---:|---|
|0LF|929|14910|5150|1308|1089|219|complete candidate audit at 1055; exact attainment checked|
|0RB|997|16539|4615|1778|1370|408|census only; observed lower bound 390|
|0RF|1837|31881|8377|1994|1645|349|complete candidate audit at 402; exact attainment and hard recurrence checked|
|1RA|2765|47151|14626|1819|1433|386|census only; observed lower bound 985|

Each census accounts for 9,765,625 complete tables. `cold_census.py` regenerates the frozen census and checks row order. Frozen bank Git blob: 56bf67275d597e354a0e827f6422ec68aa77f416. Discovery counts are not proof acceptance.

## E0=0RF: exact threshold 402 candidate

The complete frozen miss ledger is embedded in `generate_zeroRF.py` (blob 1187aaf9b338c4df1f8f584067e235fe18a8ff1a). Of 349 misses, 327 are covered by 41 reused/mutated FAR codes, 11 by sparse n-gram closure, 10 by run-length bidirectional DFA closure, and one by an exact symbolic growth theorem. These classes partition the frozen row IDs. The generator replays all certificates, verifies census hashes and emits a sharded original-source proof of `BB6.Agent8Raw54.ZeroRF.cover` and `exact_threshold`. Acceptance requires the complete root audit, not the successful discovery searches.

### Hard miss 13 — unbounded alternating growth

`1RB0RB_1RC1RE_0RD1RA_1LD0LE_0RF0LE_1LB---`

Write the zipper with left word headed by the scanned symbol. Define Z=000000000011, P=000000011, Q=0011, J=0000011. The two state-A sections both have left word 011. Their right words are
- E(n): Z P^(n+2) Q^(n+2) 11
- O(n): Z P^(n+2) J Q^(n+2).

Blank entry reaches E(0) after 664 steps. For all n≥0 the exact return costs are E(n) → O(n): 64n+216 and O(n) → E(n+1): 62n+258. Consequently E(n) → E(n+1) costs 126n+474. The proof decomposes each phase into 12 compositions of finite arbitrary-tail local transitions and pumped block sweeps. In particular P is transferred to a left 011111111 block, Q to 0111, and the return sweeps restore both counters and increment them together. No finite simulation cutoff is used to justify the induction.

`Raw54ZeroRF13.lean` (blob 429816abd25c50b6905160f2f6e440b9a5de3f0e, commit 53474da94af50254a83c355f9b0a8fc65dcfb693) compiled locally with Lean 4.36.0-rc2 against the original SweepPumping dependency from RF artifact 15143833177. The theorem `BB6.Agent8Raw54.ZeroRF13.never` has axioms propext and Quot.sound only. It excludes halting for every compatible completion, including the arbitrary F1 slot.

### Sharp attaining completion

`1RB0RC_1RC1RA_0RD0RE_1LD0LE_0RF0LE_1LAHHH` reaches its halt after 401 nonhalting moves and has blank-delay 0. The original-source witness and local cylinder Cover at weighted score 402 are proved by `Raw54ZeroRFLate.lean` (blob e9d24b6d4e4c99047487090f20de1860b038c49d; commit e234a5d87a43909312b0e58894976382494f5ef9). Both `M402.attained` and `M402.cover` compiled against the same artifact; axioms propext, Classical.choice, Quot.sound. This establishes the lower bound 402 for the child. The upper bound still requires full integration.

The complete 0RF source-audit run is [45901424082](https://github.com/FlareZ123/bb6/actions/runs/45901424082), dispatched from a1ef4fa2fc73d370ef3b3fc95f9b52dd6f91868c. It uses the RF closure manifest for exact source/object dependency reuse and audits both exported theorems. No root acceptance asserted yet.

## E0=0LF: exact threshold 1055 candidate

The complete `generate_zeroLF.py` ledger partitions all 219 frozen misses: 96 mutated FAR, 44 sparse n-grams, 24 generated growth, 21 run-length quotient, and 34 custom (including the exact late last-hole witness). This supersedes the earlier incomplete 78/33-miss counts.

`Raw54ZeroLFLate.lean` (blob 354130c9b06fd400c9e5bdfca8db99402a1eafb3) was locally compiled at this checkpoint against accepted RF artifact 15143833177. M166 cover and attainment have only propext, Classical.choice, Quot.sound; the witness reaches its final B1 slot after 1054 nonhalting moves with delay zero, giving the sharp candidate score 1055. The full 0LF upper-bound audit is [45900516624](https://github.com/FlareZ123/bb6/actions/runs/45900516624), dispatched from 5af1eef0b61c6010c3ee46dcbc0105336576aea4.

Previously compiled `Raw54ZeroLFGrowth13.lean` proves three exact growth families for 0LF misses 13,16,18:
```
13 1RB1RC_1RC---_0RD0RA_1LD0LE_0LF0LE_0RA0RC
16 1RB0RC_1RC---_0RD1RA_1LD0LE_0LF0LE_0RA0RC
18 1RB---_1RC---_0RD1RF_1LD0LE_0LF0LE_0RA0RC
```
The state-A zipper has left 00 and right 00 followed by 4n+2 ones. Blank entry takes 9 steps and each epoch 12n+34 steps. Their source theorems quantify over all compatible completions and use propext and Quot.sound.

## Next work

Resolve 0RB and 1RA frozen misses, reusing sibling FAR codes and small abstract closures before deriving recurrences. Consume the 0LF and 0RF full Cover only after complete exact source audit passes. No reduction of the accepted global canonical roster follows from the current child candidates.
