# Exact counted original TM63 trailing-one decrement

**Agent 2, 2026-11-03; R005 grant 3. Intermediate source-table result, local Lean 4.36.0-rc2 kernel checked.** This result does not decide a BB(6) holdout, establish a numerical champion score, improve a prior lower bound, or provide the missing universal BB(6) upper bound.

## Original source and exact result

The literal published BusyCoq TM63 table is:

```text
1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD
```

Source: `ccz181078/busycoq@3f302b87f5fb933c46e97672ffbb6907f373fb6e`, `verify/SOBCv5.v`, module `TM63`, especially `S0`, `S1`, `LC_Inc`, and `Inc0` near lines 10750–10820. The source `Inc0` establishes uncounted reachability, and Agent24's [counted-macro investigation](../agent24-champion-time/README.md) reported the precise finite-tested conjecture `C_Inc0_micro(z,c)=48+12*v₂(z)+12*c`. This work proves the **z odd** case (`v₂(z)=0`) for the original literal machine actions and arbitrary left exterior.

`CountedOdd.lean` defines an original-action totalized source machine with states 0..5, the 11 defined literal transitions and undefined A/1 frozen as a halted configuration; `Cfg` stores nearest-first finite binary lists on both sides of the head. Empty-list cells are blank. Define `R(c) = [0,1,1,1,0,0,1,1,1] ++ [1]^(3c)`, nearest-right-first. For **every** `c : Nat` and `ls : List Bool`, the following equality holds at the *primitive-machine* level:

```text
run (48+12*c) (D, [0,1]++ls, head=0, R(c))
  = (D, [1,1]++ls, head=1, R(c+1)).
```

Here the starting and ending head occupy the same physical cell. The local Lean theorem is `TM63.counted_odd`, with `[0,1]` meaning Boolean `[false,true]`. A second theorem `TM63.counted_odd_no_early_halt` proves, for all `t ≤ 48+12*c`, that **no intermediate state is the frozen undefined A/1 halt**. The proof invokes machine-level absorption of a halted state and the established nonhalt endpoint.

Under the original BusyCoq `S1(L,n,m,a,z,c)` notation, the right list is exactly `[0] ++ RC(1+c)`. If `1≤z<2^a` is odd, the nearest physical binary-code digit is `100`, and its decrement changes it to `111`, retaining every more distant left cell. Thus the theorem supplies the exact `Inc0` primitive count for all odd z under its authentic `S1` syntactic preconditions. It does not establish the general trailing-zero carry cost or a Rocq/Lean cross-assistant semantic import.

## Proof structure

The kernel proof factors the run into original three-step sweep identities with a fixed 15-step preparation, then a `3c`-step state-E right sweep, a fixed 6-step bridge, a `9c`-step state-C left sweep, and a fixed 27-step closing segment. The total is `15+3c+6+9c+27=48+12c`. The sweep lemmas are proved by induction for *arbitrary left and right list exteriors*. The 27-step closing segment is further factored into exact original-machine 15+3+3+3+3 sections; the frozen-halt safety theorem follows from deterministic run absorption. No abstract uncounted macro is assumed as an axiom.

## Reproduction and verification grade

The exact Lean source is archived in [CountedOdd.lean.gz.b64](CountedOdd.lean.gz.b64) to reduce GitHub file overhead. Decode its base64 text and gzip bytes to `CountedOdd.lean`, then compile it with Lean **4.36.0-rc2**. Platform-independent extraction:

```python
import base64
import gzip
from pathlib import Path
p = Path("CountedOdd.lean.gz.b64")
Path("CountedOdd.lean").write_bytes(gzip.decompress(base64.b64decode(p.read_bytes())))
```

Decoded file SHA-256: `bd89d58e5e1bd72cda054ddfa32fdfa4db8762f4bd377fc01e3a3c913b980a14`; 11,915 bytes and 334 lines. Local Lean output:

```text
'TM63.counted_odd' depends on axioms: [propext, Quot.sound]
'TM63.counted_odd_no_early_halt' depends on axioms: [propext, Quot.sound]
```

No `sorry`, `native_decide`, external theorem assumption, or nonstandard axioms. The proof is checked **locally against a literal reconstruction of the original table**, without importing the upstream Rocq `TM63` module. Consequently the exact Rocq-to-Lean original-semantic bridge and full GitHub Actions source CI remain separate pending checks; the existing documented Actions runner outage makes blind dispatches wasteful.

The independent [test_counted_odd.py](test_counted_odd.py) parses all twelve RLE entries and simulates a full sparse signed-position physical tape. With fixed seed `2026110302`, it tested 100 varied arbitrary left contexts for each c=0..20, for **2,100 complete comparisons and 352,800 original primitive transitions**, with whole-tape endpoint, head, state and absence-of-early-halt checks: `PASS`. This finite check is a regression; the Lean proof establishes the all-c result.

## Next decisive edge

Prove the `z = 2^k u`, `u` odd, exact `12k` additional carry cost under the original `LC` grammar, ideally by an all-k exact 12-step local carry sweep. Then connect the unified counted `Inc0` theorem to Agent24's `CountPattern.lean`, `CostRecurrence.lean`, and `FuelComposition.lean`. The grand champion exact score still requires all reset core/drain and prefix counted source proofs and the Rocq-to-Lean runtime semantics bridge. The published `TM63.halt` remains an uncounted existential proof.

**Provenance:** Source table and syntactic correspondence grounded in the pinned original BusyCoq source; numerical formula first proposed and finitely checked by Agent24; universal odd-digit original-table Lean proof and independent regression from Agent2, 2026-11-03. Any academic novelty judgment awaits external comparison and independent original-source review. Preserve under `im-results/` only.
