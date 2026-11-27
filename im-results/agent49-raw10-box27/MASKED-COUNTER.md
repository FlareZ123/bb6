# Masked binary counter, Raw10 Box27

**Mathematical result, source candidate:** the two one-hole cylinders

```
[8,-1,11,24,13,13,14,17,22,9,19,4]
[8,-1,11,24,13,13,14,17,22,17,19,4]
```

are nonhalting for every completion (50 ordinary normalized transition tables). The missing entry A1 is never queried. These are distinct from the earlier E0=21 five-hole slice and from the three sweepers in Box27HardGrowth.lean.

At t=6 the authentic blank orbit is in E, scanning zero with a blank left half-tape. The right stack is represented as a low bit b followed by little-endian two-bit digits (x,y) encoded 0xy. The physical bit positions 1 mod 3 are zero. E with a zero low bit toggles it in two steps. E with a one low bit takes three steps to B, reading the low bit x of the first digit, with two ones on its left. At this carry state:
- x=0: B0,C1,D1 set x to one, leave y unchanged, restore E.
- x=1,y=0: B1,F0 and a three-step left unwind restore E with digit (0,1).
- x=y=1: B1,F1,A0 consume the fixed separator of the next digit, append three ones to the left, and recurse. After the recursive return, three leftward steps clear those ones into a zero digit.

The unwind is E1,C1,D1 for E1=0LC and three E1 steps for E1=0LE. All are exact framed identities with arbitrary untouched tails.

For any requested number N of epochs, pad the original blank with N reserved zero digits. Each return incorporates at most one reserved zero digit, so the carry terminates and the E grammar is preserved at every one of N positive-cost epochs. The padded tape represents the same infinite blank. Consequently arbitrarily long live primitive prefixes exist and every compatible completion is nonhalting. No finite simulated cutoff is a premise.

Box27MaskedCounter.lean: carry_return and padded_live compiled locally in Lean 4.36.0-rc2 using a fixture containing the original Move, Z0, move0, step0, run0 and join0 definitions/proof, with only propext and Quot.sound. The final never theorem imports the actual SweepPumping module and uses its original zipper transport; exact full source closure and axiom audit are still required. Local direct Git clone was blocked by DNS. Manual source audit [run 46070352006](https://github.com/FlareZ123/bb6/actions/runs/46070352006) at revision 34a28a93ee7685ba6c8ea41b604b37d684e0e995 checks that closure. Do not count these as accepted parent covers yet.
