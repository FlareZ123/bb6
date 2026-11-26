# Raw40 binary-counter leaves 486 and 487
Two difficult F1-free leaves of 0LB/1RB:
```
1RB0LB_1RC1RB_0RD1RE_1LD1LA_0RF0LE_0RA---
1RB0LB_1RC1RB_0RD1RE_1LD1LA_0RF0LE_0RB---
```
Raw40BinaryPair.lean proves universal nonhalting for both using blank entry at 31 steps and an arbitrary finite LSB-first bit list invariant. Increment maps [] to [0], 0w to 1w, 1w to 0 increment(w). A encodes 0 as 000 and 1 as 100; B encodes 0 as 000 and 1 as 001. Configurations at F have left zipper 00 and right zipper 0^6 encA(w)1 or 0^3 encB(w)1. With k leading ones, costs A 32+8k (zero exists), 40+8k (overflow); B 26+8k or 28+8k. Positive recurrence cost proves all 25 choices of F1 nonhalting in each variant. Lean 4.36.0-rc2 locally checked epoch and never using Agent46AutoPump, axioms propext and Quot.sound. The parent all-branch audit is separate.
