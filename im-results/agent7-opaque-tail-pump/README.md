# Raw36 D1=0LA: source-checkable opaque-tail pumping and exact candidate complement

**Scope:** intermediate research. This dossier does **not** claim the direct D1=0LA parent `Cover`, the Raw36 global parent, or BB(6).

## Exact computational frontier

The original canonical D1=0LA tree is the successful scout [run 46122807180](https://github.com/FlareZ123/bb6/actions/runs/46122807180), artifact `15254765346`, literal parent `1RB---_1RC---_0RD---_0LD0LA_------_------`, candidate weighted threshold **1985**, 2,255 distinct OPEN literals, sorted-key digest `d3cff2c1257272d8af4c8087906589d4623f41dcd8cd3de98e2ae7f71d8d8ff0`.

The already archived FAR bank ([run 46123250654](https://github.com/FlareZ123/bb6/actions/runs/46123250654), artifact `15255135843`) gives 1,773 candidate keys. The original N-gram bank ([run 46123330768](https://github.com/FlareZ123/bb6/actions/runs/46123330768), artifact `15254647345`) gives 883 candidates, with 706 duplicates against FAR: union **1,950**. Structured invariant search ([run 46136679879](https://github.com/FlareZ123/bb6/actions/runs/46136679879), artifact `15260191857`, 100 exact learned recipe seeds) supplies another 256 previously unmatched candidates. Thus 2,206/2,255 have **computational candidate** certificates, not yet necessarily accepted source proofs; **49** remain outside these three banks.

`d100-new-pumps.txt` lists **seven** different literals from those 49 for which an exact **all-suffix primitive-machine pumping theorem** was compiled locally with Lean 4.36.0-rc2 against the previously original-source-accepted `SweepPumping` objects (artifact `15255990116`). Every exported `never` uses only `[propext, Quot.sound]`, with no `sorryAx` or `native_decide`. Their merged original-semantics Lean source has SHA-256 `3ba6cb6ae32b6b094a21116ee0f0a146e76142be6e3edcdfed889c1be063cfc3`. These seven shrink the **candidate complement** to **42**, sorted exact-key SHA-256 `eedd63279c7d58f8c3588a337439bc40b82b4265c9249cb24c255090e61c41ed`. These are seven new *literal nonhalting proofs*, not a complete parent Cover.

## The proof method

For a source zipper state `(q, F, P ++ T)` actually reached after `E` steps from the blank tape, prove for **all** finite bit lists `R` the exact `D > 0`-step law
`run0 table D (q, F, P ++ R) = some (q, F, P ++ W ++ R)`
where `W` is a nonempty word. Then `family n = (q,F,P ++ W^n ++ T)` grows for every `n`; applying the existing `never_of_growth` proves `NeverHalts` for **every total completion** compatible with this partial table. The reflected left-ray form is also supported.

`detect_pump.py` searches real blank-run snapshots and rejects candidate macros that would read an opaque `?` at the unknown tape suffix. The search is **heuristic and bounded**, so failure to find a pump proves nothing. `pump_emit.py` emits a Lean all-suffix macro `by rfl`, separately source-checkable blank entry chunks, growth induction, and `NeverHalts`. The emitted Lean theorem, **not** the Python scanner, establishes correctness. The original 902-step Raw36 D1=0LB pump is merely a regression, not counted again.

For one literal proof:

```bash
python im-results/agent7-opaque-tail-pump/pump_emit.py \
 '1RB1LE_1RC0RB_0RD0LE_0LD0LA_1LF1LA_1LB---' \
 /tmp/Raw36D100Check.lean BB6.Agent7Raw36D100Check
```

The existing manual workflow `.github/workflows/agent7-raw36-drift902.yml` has a D100 batch mode intended to download the pinned exact census, check **all seven literal keys** against it, generate the merged `Raw36D100NewPumps.lean`, compile its **full original-source import closure**, and audit each `never` axiom list. The CI source-audit result, when available, is decisive for labelling these certificates source-accepted.

**Next:** accept all viable FAR/NG/structured candidates through a source-checked parent/child audit; attack the strict 42-key complement without rerunning earlier 2,206 candidates; pass these seven names to the exact parent proof generator. Do not report a direct parent or BB(6) upper bound until its whole Cover is accepted.
