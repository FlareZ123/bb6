# Machine I: complete blank-orbit nonhalting via an inductive payload grammar

**Status (2026-11-28):** complete, locally kernel-checked nonhalting theorem `MacroI.neverBlank_I` in the literal six-state stream model under Lean 4.36.0-rc2. The original repository-model bridge and parent-cover consumption are separate outstanding steps. This closes the mathematical blank-orbit problem for this exact table; it does not establish a new global BB(6) bound.

## Exact machine and return boundary

```text
[8,24,11,18,1,13,17,3,12,0,4,21]
1RB1RF_1LC0RE_0LA0LD_0LE1LA_1RC---_1RA0LF
```

Streams are nearest-first, the right stream includes the scanned symbol, and `z` is the infinite zero stream. Define
```text
phase(j,r) = A(z, 01010010 (0010)^j r)
N(j,u) = phase(j,10101 u)
```
The authentic blank configuration reaches N(3,11 z) after exactly 490 transitions.

## Closed language and unbounded carry

The payload language consists of a finite sequence of arbitrary members of {ZS,ZR,PS,PR}, followed by one of ten terminal words and the infinite blank suffix. Here ZS=00001000, ZR=00000101, PS=00101000, PR=00100101.

Every payload decomposes into PR^k x. The terminal relation (x,y,t) is:
- 0000 r → 0010 r, t=14 (covers ZS and ZR)
- 00101000 r → 00000101 r, t=36
- 11 → 01, t=8
- 01 → 00001, t=18
- 00001 → 00101, t=14
- 00101 → 00000101, t=36
- empty → 001, t=14
- 001 → 0000101, t=30
- 0000101 → 0010101, t=14
- 0010101 → 0000010001, t=40
- 0000010001 → 0010010001, t=14
- 0010010001 → 0000100011, t=34

The first two preserve arbitrary tails; the ten remaining cases have blank tails. Every y belongs to the language. The fully quantified theorem `complete_carry` gives
```text
run (236+t+24*k+64*j) (N(j,PR^k x))
  = some (N(j+2,ZS^k y)).
```
The forward carry costs 10 per pair and the backward carry 14. The initial sweep, terminal core, final sweep and two packet boundaries account for the remaining cost. `payload_decompose` proves this covers the entire inductive language, `payload_return` establishes its preservation, `good_progress` gives a strictly positive successful return, and `neverBlank_I` uses strong induction on arbitrary primitive time. No finite simulation horizon is used.

## Reproduce

```bash
cd im-results/agent13-raw10-box33
python3 unpack_i_parametric.py
python3 unpack_i_relay.py
python3 unpack_i_invariant.py
export LEAN_PATH=.
lean -o Box33D17V12IParametric.olean Box33D17V12IParametric.lean
lean -o Box33D17V12IRelay.olean Box33D17V12IRelay.lean
lean -o Box33D17V12IClosed.olean Box33D17V12IClosed.lean
lean Box33D17V12IInvariant.lean
```

The new archive extractor checks SHA-256 for both sources. All three audited theorems (`complete_carry`, `payload_return`, `neverBlank_I`) have axiom profile [propext, Classical.choice, Quot.sound], with neither sorryAx nor native_decide. The proof source is in the original literal stream model, pending an independently checked source-model transfer.

## Earlier partial results and their limits

The previous odd/even packet proofs have costs 108+32j and 110+32j. The relay lifting theorem in Box33D17V12IRelay turns an arbitrary-tail core of cost c into a full return of cost 20+c+16j; universalSecond costs 48+16j. The carry example in Box33D17V12ICarry has cost 132+32j. These are now subsumed for blank-orbit purposes by the language proof, but remain independently useful.

Synthetic phase(0,0x195) (nearest-bit-first encoding) halts after 29 steps, so blanket claims for every tail congruent to 21 mod 32 are false. Likewise, payload prefixes 0011 and 010011 can halt. The language invariant is essential: the earlier 100,000-return experiment and finite prefix search did not prove it.

The other outstanding hard table in D17/E0=12 is [8,24,11,8,1,13,17,18,12,5,2,0]. Neither that table nor the complete cylinder is closed by this proof alone.
