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

Two Lean implementations certify the same whole-zipper identity. [`FrontierOdd0100.lean`](FrontierOdd0100.lean) imports Agent39's independently copied 12-row table. Its locally compiled theorem `BB429Odd0100.odd_0100_root` uses arbitrary-suffix two-step induction and fixed transitions. More importantly, [`FrontierOdd0100Source.lean`](FrontierOdd0100Source.lean) imports the actual unchanged-repository `BB429OddExcursion` source interpreter and Agent33's certified `CZeroEvenReturn.a_right_pairs_exact`. Its theorem `BB429Odd0100Source.odd_0100_original` proves the exact **original source zipper** statement, also for all parameters and suffixes. It compiled locally against faithful copies of the original source definitions and imported theorem statements using Lean 4.36.0-rc2, reporting only `[propext, Quot.sound]`. The existing manual `agent1-429-w4-scanE.yml` workflow was extended to compile the original-repository dependency graph and dispatched; its CI verdict is pending. The physical `BB6Coverage.run` lift and first-return interior exclusion remain separate proof obligations.

## Relation to other frontier cases and genuine root

Agent39's [even-prefix return and fatal odd-prefix family](../agent39-429-frontier-left/README.md) establish that C/0 left stack `(11)^m 0 gamma` safely returns after 4m+7 moves, while a specified `1^(2j+3)000 gamma` configuration reaches fatal C/01. The new branch treats the separate odd-prefix `(11)^m 10100 gamma` family and preserves its arbitrary remote suffix, potentially useful in a larger C/0 first-return language.

A different odd-prefix `1^(2m+1)010 gamma` with unrestricted gamma cannot be silently substituted: the extra zero before gamma is used by the fixed fourteen-step turn. The exact full-tape premise matters.

The authentic **blank-root** #429 machine halts precisely when its actual trajectory reaches C scanning zero with an immediately marked right neighbor ([Agent32's original-source result](../agent32-429-raw-parent/README.md)). No proof yet establishes that the real blank orbit enters only the known safe frontier families or excludes every exceptional fatal input. Therefore this result does not prove #429 nonhalting or determine BB(6).

## Strongest next test

Prove, using an original-source guarded interpreter or a parametric head-maximum monitor, that the 4m+21 segment has no intermediate C/0 and its terminal head is an all-prefix new right record. Then connect that safe case to a **complete original blank-root frontier grammar**, including the exceptional suffixes that fall outside this family. The original physical first-event partition is the missing mathematical quantifier. Keep this intermediate result in `im-results/`.


## New 9 November source-to-physical root-frontier extensions

The all-suffix odd-`0100` theorem has now been strengthened across the original physical six-state implementation:

- [`FrontierOdd0100Max.lean`](FrontierOdd0100Max.lean) establishes the **exact signed head displacement +3 and entire-primitive-prefix maximum +3** throughout the `4m+21`-step section.
- [`FrontierOdd0100Physical.lean`](FrontierOdd0100Physical.lean) lifts the exact endpoint and prefix bound to the real infinite physical tape, for any configuration represented by the complete input word. [`FrontierOdd0100Root.lean`](FrontierOdd0100Root.lean) further proves that **if the starting C/0 is an actual blank-root global right-record**, the terminal C/0 is also an actual later global right-record, at head +3, with all earlier heads below that position.
- These three facts, including the authentic-root conditional, compiled in the original repo against unchanged source and no `sorryAx`; [CI 42651271940](https://github.com/FlareZ123/bb6/actions/runs/42651271940) subsequently failed at an unrelated *missing .olean dependency for the next optional C/0 census module*. They are source-checked individually in that job, and a consolidated passing job is being pursued.

A broader exact all-suffix parity parser is given by [`OddCZeroToE1.lean`](OddCZeroToE1.lean). From a right-blank C/0 whose entire left tape is `1^(2m+1) 0 gamma` nearest-first, the **real table** reaches state E scanning 1 after exactly `2m+6` primitive instructions, preserving `gamma` on its left and producing right word `1 (10)^m 01`. [`OddCZeroToE1Max.lean`](OddCZeroToE1Max.lean) proves signed head displacement `-(2m+2)` and a sharp bound `+1` on every intermediate head. The original infinite-tape lift is [`OddCZeroPhysical.lean`](OddCZeroPhysical.lean), compiled with no `sorryAx` in the above original-source CI run. [`OddCZeroRoot.lean`](OddCZeroRoot.lean) packages the exact true-blank-origin conditional and prefix head bound.

A second **exceptional base** closes the one-one-left case followed by three zero cells: `C/0 | 1000 gamma | right blank` takes exactly **16 steps** to `C/0 | 11111011 gamma | right blank`, ending at head +4 with every primitive head at most +4. [`Base1000.lean`](Base1000.lean) contains this literal fixed 16-step `runWithMax` identity, an exact first-C/0 `runCount=1` identity, and original-physical lift. The fixed identities compiled locally against the exact source-table definitions; full original-source audit is pending. This exceptional base contrasts with the previously source-certified fatal family `1^(2k+3) 000 gamma`: the **length-one odd block is a safe return** whereas every longer odd block of length at least three followed by three zeros reaches a fatal C/01 event.

[`OddFrontierCensus.lean`](OddFrontierCensus.lean) proves **exactly one** C/0 instruction start in each odd-`0100` and odd-to-E/1 section, namely its entry; the endpoint of an odd-`0100` section is the next C/0. This uses public wrappers for the preexisting symbolic C/0-free A/F and A/B sweeps, and its original-source CI audit is pending.

These are parametric original-table dynamics and **conditional** genuine-blank-root implications, not a total blank-root reachability grammar. They do not decide machine #429 or BB(6). The main unresolved mathematical task is to prove an invariant covering *every* possible genuinely rooted C/0 section, including alternating deep-left tails, or identify an authentic fatal root.
