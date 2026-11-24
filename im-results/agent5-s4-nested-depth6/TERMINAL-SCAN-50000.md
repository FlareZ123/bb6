# 50,000-R-block terminal-quotient scan

**Status:** intermediate computational result only. This does not prove S4 nonhalting or determine BB(6).

## Reproduction

The manual workflow `.github/workflows/agent5-s4-terminal-scan.yml` completed successfully on 2026-11-24:

- workflow run: `45377170690`
- checked-out commit: `0dcc02a2938b5a3744ce6676394222d1c809557d`
- job: `terminal-scan` (`138386428362`)
- source bridge: `s5457_root_extension.mjs`
- reduced simulator: `s4_nested_macro.cpp`, mode `--scan-terminal-50000`

The workflow first reproduced the finite root bridge from the source-certified return-5457 state to the stored 24-digit `blockRoot`. The C++ program then constructs the 4,603-gate R word and its authentic modeled tail after 107 Q blocks, and applies 50,000 R blocks. Each R block contains 4,603 effective gates, for **230,150,000 gate applications**.

This is exact-integer computational evidence conditional on the finite root bridge and the computed Q/R reductions. The workflow itself explicitly labels the bridge as deterministic BigInt replay, not a Lean-kernel proof. The C++ run uses `uint64_t`; its reported total mass remains below the 64-bit limit. Do not promote this scan to a source-level or all-time theorem.

## Terminal events

The scan found 13 full-suffix events, no halting event, and no exact power-of-two terminal quotient. The exact event records are:

| R block | Gate | Suffix length | Quotient (q) | (v_2(q)) | Odd part (q_{m odd}) | (q_{m odd}\bmod21) | (q\bmod31) | (q\bmod127) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 81 | 8 | 1,614,438,017,023 | 0 | 1,614,438,017,023 | 13 | 13 | 33 |
| 0 | 245 | 9 | 7,360,772,220,328 | 3 | 920,096,527,541 | 2 | 27 | 68 |
| 0 | 4,144 | 13 | 101,547,537,247,058 | 1 | 50,773,768,623,529 | 7 | 19 | 19 |
| 4 | 4,148 | 15 | 285,089,326,853,366 | 1 | 142,544,663,426,683 | 7 | 21 | 13 |
| 10 | 2,019 | 17 | 853,437,117,523,135 | 0 | 853,437,117,523,135 | 19 | 15 | 98 |
| 36 | 3,425 | 18 | 2,584,030,328,097,256 | 3 | 323,003,791,012,157 | 17 | 11 | 100 |
| 393 | 4,493 | 22 | 17,529,889,155,809,509 | 0 | 17,529,889,155,809,509 | 10 | 26 | 79 |
| 2,195 | 1,819 | 23 | 433,593,729,656,808,345 | 0 | 433,593,729,656,808,345 | 9 | 22 | 5 |
| 2,654 | 168 | 24 | 400,997,681,403,749,147 | 0 | 400,997,681,403,749,147 | 11 | 2 | 48 |
| 7,533 | 2,393 | 25 | 853,610,397,800,397,087 | 0 | 853,610,397,800,397,087 | 18 | 0 | 75 |
| 12,259 | 2,650 | 26 | 1,658,129,806,009,771,385 | 0 | 1,658,129,806,009,771,385 | 11 | 3 | 62 |
| 13,369 | 617 | 27 | 1,533,256,918,913,496,363 | 0 | 1,533,256,918,913,496,363 | 6 | 28 | 123 |
| 22,293 | 477 | 28 | 2,598,795,037,001,405,382 | 1 | 1,299,397,518,500,702,691 | 0 | 12 | 62 |

Summary emitted by the run:

- blocks: 50,000
- gates: 230,150,000
- full-suffix events: 13
- exact power-of-two quotients: 0
- (q\bmod31) power-of-two candidates: 1
- (q\bmod127) power-of-two candidates: 0
- (q_{m odd}\bmod21=2): 1
- maximum suffix length: 30
- final suffix length: 30
- final suffix mass: 13,743,897,600,618,269,200

The odd-part histogram modulo 21 was:
[
0:1, 2:1, 6:1, 7:2, 9:1, 10:1, 11:2, 13:1, 17:1, 18:1, 19:1,
]
with all other residues absent.

## Mathematical interpretation

The observation that the first two root-extension terminal odd parts were both (2\pmod{21}) does **not** persist: only one of these 13 later events has that residue. The proposed universal (q_{\rm odd}\equiv2\pmod{21}) obstruction is therefore falsified.

No event in this finite horizon has (q\bmod127\in\{1,2,4,8,16,32,64\}), the residues necessary for (q) to be a power of two. This is only a finite filter observation, not a modular invariant; 13 samples are insufficient to justify pursuing it as one.

The useful conclusion is negative: do not spend further compute on the mod-21 odd-part conjecture. A future modular proof would need a structural invariant of the reduced suffix map, not extrapolation from this histogram. The scan also provides a reproducible finite stress test of the R-word suffix model, but it does not establish survival beyond the modeled horizon.
