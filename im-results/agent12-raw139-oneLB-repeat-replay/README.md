# Repeated local-window replay: exact Raw139 last-hole certificates

## Result

Two formerly expensive one-hole traces have checked original-semantics weighted certificates:

| Residual | Exact table codes | Final query after moves | Slot | Weighted bound |
|---|---|---:|---|---:|
| 209 | [7,20,11,1,14,9,17,16,6,11,0,24] | 31790091 | F1 | 31790097 |
| 892 | [7,23,11,13,14,21,24,16,6,11,3,0] | 3643339 | D0 | 3643345 |

Exports: `BB6.Agent12RepeatReplay.R209.parent`, `R209.all_completions_weighted B hb`, and corresponding `R892` names, where the proof hb is the displayed bound <= B. The table is represented with `fromCodes` exactly as in the existing Raw139 proof. At a filled last hole, all entries are ordinary moves and no halt occurs. If it is a halt, the checked reach theorem fixes the unique query time; any blank delay is at most five.

## Method

A finite prefix window is evaluated over arbitrary exterior rays. A rule consumes a word on one side, produces another word on the other, and preserves fixed anchor prefixes and the state. The Lean theorem `repeat_sound` proves arbitrary repetitions by induction. The packed checker matches entire repeated prefixes by modular arithmetic and reconstructs output using a geometric series, avoiding explicit tape expansion. Each dictionary rule is checked once with finite local semantics. Commands either repeat a dictionary rule or run exact primitive packed moves. The `execute_sound` theorem composes the steps and exact counts; `run_sound` translates to original physical machine semantics. The last-hole theorem is table-independent.

The C++ discovery program emits untrusted proposals by compressing repeated identical read-slot motifs. A final unread endpoint can disagree with the next repetition's assumed anchor; the Python generator repairs that case by using one fewer repetition followed by exact primitive moves. All actual commands, anchors, endpoints and counts are checked in Lean; neither C++ nor Python is part of the trusted proof.

209: 16 rules, 15780 commands, 124 checked blocks. Local generated module elaboration: 21.55 s, peak RSS 2546460 KiB.
892: 30 rules, 5634 commands, 45 checked blocks. Local generated module elaboration: 17.99 s, peak RSS 2004176 KiB.
Both final weighted theorems depend only on propext, Classical.choice, Quot.sound. Reach theorems depend only on propext, Quot.sound. Lean 4.36.0-rc2, pinned original-source artifact 15169732599 (run 45934344615).

## Reproduce

Use Lean 4.36.0-rc2 with the original dependency build and modules from sibling directories `agent12-raw139-oneLB-c1-286` (Counter286, Counter286Bridge) and `agent12-raw139-oneLB-lateA1` (LateCert). Put the corresponding compiled modules and artifact build directory on LEAN_PATH. In this directory:

```sh
lean -o RepeatReplay.olean RepeatReplay.lean
g++ -O3 -std=c++17 discover.cpp -o discover
./discover 0 > c209.txt
./discover 1 > c892.txt
python3 gen_repeat.py 209 c209.txt Late209Checked.lean
python3 gen_repeat.py 892 c892.txt Late892Checked.lean
lean -o Late209Checked.olean Late209Checked.lean
lean -o Late892Checked.olean Late892Checked.lean
```

Source blobs: RepeatReplay.lean bb83b261b7a78bf814f86bab66f70f139dded660; discover.cpp b672c458b5b63cf1aa153f71d9a12a8820ffef46; gen_repeat.py 18d57c2650626b15cb6764bab0eba047f8cb4802. The C++/Python front ends currently specialize to these two tables. The Lean checker is general.

These are local kernel-checked source-level certificates using an original-source dependency closure. Parent graft and global reduction are separate obligations; no such reduction is claimed here.
