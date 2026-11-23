# Cryptid D: 64 kernel-certified terminal right-prefix cylinders

**Status (2026-11-23):** a genuinely source-checked, *intermediate* theorem about prepared boundary configurations. The authentic blank-tape orbit has **not** been shown to enter this family, so this work neither decides Cryptid D nor determines BB(6). External priority/novelty has not been established. The mathematical certificate remains under `im-results/`, not `results/`.

## Statement

Use the original six-state, two-symbol D table
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, with A=0,...,F=5 and tape bits 0=false, 1=true. An E-boundary configuration scans **0** at absolute coordinate zero, has the left-neighbor word (nearest first)

`00(10)^m11` with `m >= 3`,

and has the right-neighbor word (nearest first)

`1011011 w y`,

where `y` is **any finite Boolean word**, followed by the usual infinite blank tape. For each `w` in a fixed, explicit **prefix-free set of 64 words of length at most 12**, the machine reaches state F scanning a 1, with no defined next instruction, after exactly `t(w)` primitive machine transitions. The certified `t(w)` range is **74 through 177**, and the right-tail independence is proved for all `m >= 3` and all `y` (no length bound).

This is an infinite family of configurations, *not* merely 64 isolated finite simulations. The corresponding product cylinders have prefix-free Bernoulli measure `1227/4096` relative to independent uniform right-hand words after the fixed `1011011` prefix. This measure is a combinatorial property of the table, **not** the probability of entering the family from the blank tape.

## Lean theorem and trust

Source: [TailWindowPrefix.lean](../agent32-cryptid-padding/TailWindowPrefix.lean), importing Agent32's previously accepted [TailWindowCore.lean](../agent32-cryptid-padding/TailWindowCore.lean).

- `prefixTable` is the explicit list of 64 pairs `(w,t)`, with pairwise non-prefix initial words; word lengths are 3:1, 5:2, 6:2, 7:3, 8:6, 9:6, 10:11, 11:14, 12:19.
- `prefixTable_checked` is one computed **Lean proof**, not a simulator assertion: for each listed pair it proves positive time and `haltCheckWord t w = true`. The certificate examines the actual raw transition table and the entire finite path within window `[-5, 7 + |w|]`.
- `initialWordEqOn` proves that the local finite-window tape and the actual alternating-left tape with an arbitrary appended right word agree on the entire audited interval.
- `halts_with_arbitrary_suffix` transports certified finite paths by the previously proven all-step `runEqOn` and establishes that the resulting F/1 head is truly terminal.
- `all_prefix_table_halting` combines all of this for **every** `(w,t)` in `prefixTable`, every eligible left-stack length, and every arbitrary right suffix.
- Lean 4.36.0-rc2 [manual CI **45264135125**](https://github.com/FlareZ123/bb6/actions/runs/45264135125) **passed** on 2026-11-23. `#print axioms prefixTable_checked` reports only `[propext]`; `#print axioms all_prefix_table_halting` reports `[propext, Classical.choice, Quot.sound]`. Neither uses `sorryAx` nor `native_decide`. Run with the existing `agent32-cryptid-padding.yml` manual target `tail_prefix_cylinders`.

These theorems certify a **prepared E-boundary**, not the full root. In particular, merely knowing that the enormous upstream TM62 `A(3^108 k+C,[])` halting class exists does not license appending arbitrary right tails to its 107 symbolic reduction. A direct attempt to replace every intermediate source `A(…,[])` checkpoint by `A(…,ls)` in [SuffixParametricPrefix.append.lean](../agent32-cryptid-padding/SuffixParametricPrefix.append.lean) **failed to compile** (manual CI 45262562151); it is not a theorem and its hypothesis is not currently established. Do not splice its draft conclusion into the halting proof.

## Stronger next question: an unbounded scanner before the terminal word

A separate **computational hypothesis** from exact transition-table experiments (not formalized): for any `q >= 0`, an E/0 boundary with the same immediate two left zeros, and right-neighbor prefix `(10)^q 1101101100`, enters F/1 after **`72+2q`** primitive steps, independent of the rest of the right tape, provided the left stack is long enough. For q=0,...,7, the explicit traces all have minimal head position -2 and maximum position `10+2q`. The source upstream lemma `step_B10_01B` already proves the unbounded two-step-per-pair B scan. After its initial five steps and the q scan, the remaining 67-step terminal segment is plausibly uniform. **This is not yet a Lean theorem**; check the exact source decomposition before asserting it, and avoid treating eight numerical cases as an induction.

The relevant next problem is not to grow a finite trace blindly. It is to compose the universal terminal lemma with an actually blank-reachable feeder. Existing source-return grammars for the root are highly constrained; an A-section / E-prefix bridge must preserve the position of the scanned zero and the delimiter, rather than adding or deleting a zero by visual similarity. Conversely, if an E-prefix feeder can be proved from the blank tape, this finite-window certificate gives a rigorous halt immediately.
