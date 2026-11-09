# #429 C/0 fresh-right return with odd 0100 left boundary

## Proven conditional return

The six-state two-symbol table is `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. The `Frontier429` source-compatible zipper from Agent39 stores the nearest scanned left and right cells first, followed by implicitly blank cells. Its state code 2 denotes C.

For **every natural m** and **every finite left suffix gamma**, consider C scanning zero with blank right tape and left stack

```
(11)^m 10100 gamma
```

(the notation denotes nearest-first bits, not physical left-to-right printed tape). The source transition table executes exactly **4m+21 successful primitive instructions** and reaches **C scanning zero** again, with right stack empty and left stack

```
10 (11)^(m+3) gamma.
```

The physical head is three positions right of the entry head. This last assertion follows by the exact finite stack-length displacement balance of the displayed transition (and can be separately formalized if needed); the Lean theorem currently certifies the complete zipper endpoint and elapsed instruction count.

The theorem `BB429Odd0100.odd_0100_root` in [FrontierOdd0100.lean](FrontierOdd0100.lean) is a natural-number induction for the two unbounded sweeps, composed with exact fixed 3-, 14-, and 4-step transitions. It uses `Frontier429.af_sweep` and the existing `Frontier429.ab_sweep`. The proof was compiled locally using Lean 4.36.0-rc2, with axiom output `[propext, Quot.sound]` and no `sorry`. An unchanged-original-source import/physical representation CI audit is still pending. In particular, this is a source-table-matching model theorem, not yet a verified `BB6Coverage.run` original-physical theorem.

## Relation to other frontier cases and genuine root

Agent39's [even-prefix return and fatal odd-prefix family](../agent39-429-frontier-left/README.md) establish that C/0 left stack `(11)^m 0 gamma` safely returns after 4m+7 moves, while a specified `1^(2j+3)000 gamma` configuration reaches fatal C/01. The new branch treats the separate odd-prefix `(11)^m 10100 gamma` family and preserves its arbitrary remote suffix, potentially useful in a larger C/0 first-return language.

A different odd-prefix `1^(2m+1)010 gamma` with unrestricted gamma cannot be silently substituted: the extra zero before gamma is used by the fixed fourteen-step turn. The exact full-tape premise matters.

The authentic **blank-root** #429 machine halts precisely when its actual trajectory reaches C scanning zero with an immediately marked right neighbor ([Agent32's original-source result](../agent32-429-raw-parent/README.md)). No proof yet establishes that the real blank orbit enters only the known safe frontier families or excludes every exceptional fatal input. Therefore this result does not prove #429 nonhalting or determine BB(6).

## Strongest next test

Prove, using an original-source guarded interpreter or a parametric head-maximum monitor, that the 4m+21 segment has no intermediate C/0 and its terminal head is an all-prefix new right record. Then connect that safe case to a **complete original blank-root frontier grammar**, including the exceptional suffixes that fall outside this family. The original physical first-event partition is the missing mathematical quantifier. Keep this intermediate result in `im-results/`.
