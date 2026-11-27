# Four-phase nested binary counter (Raw13 E1=1RA)

Two further unresolved leaves share the same exact four-phase counter language:

- `1RB1LD1RC0LE1LA1RE0RF0LA0RD1RA---0RB` (B1=0LE)
- `1RB1LD1RC1RB1LA1RE0RF0LA0RD1RA---0RB` (B1=1RB)

Both have F0 unassigned. Let P=010111, D0=01010101, D1=01010111, and encode a little-endian bit list by these eight-bit digits. Head-inclusive left and head-exclusive right are nearest-first. The common phase frames are:

| Phase | State | Left | Right |
|---|---|---|---|
| 0 | F | 10 | P encode(bits) 1 |
| 1 | A | 000 | P encode(bits) |
| 2 | A | 000 | P encode(bits) 011 |
| 3 | A | 000 | P encode(bits) 01011 |

The seed is phase 0, no digits, at primitive transition 32. Normal increment, preserving the phase and arbitrary higher digits, replaces D1^j D0 by D0^j D1. Its exact cost is 20j+46 (0LE) or 18j+44 (1RB). At all-ones overflow of width k, reset all k digits to zero and advance to the next phase; phase 3 appends one extra zero digit on returning to phase 0.

| Overflow | 0LE | 1RB |
|---|---:|---:|
| 0→1 | 20k+29 | 18k+29 |
| 1→2 | 20k+34 | 18k+34 |
| 2→3 | 20k+42 | 18k+38 |
| 3→0 (width k+1) | 20k+47 | 18k+45 |

These are **all-width symbolic traces**, not extrapolations. Each is a sequence of bounded primitive steps and two whole-block transfers: the rightward transfer consumes a D1 block and produces eight ones in 12/10 steps; the leftward transfer consumes eight ones and produces D0 in 8 steps. Their finite pre/post contexts are recorded in the literal Lean macro bank. The carry macros prohibit reading the arbitrary higher-digit tail. Every symbolic exponent is arbitrary, including zero. Soundness is reduced to the existing kernel-checked knownRun and sweep lemmas.

If F(k) denotes the time to fill k zero digits to all ones, then F(0)=0 and F(k+1)=2F(k)+ak+b, with (a,b)=(20,46) or (18,44). Thus F(k)=(a+b)(2^k-1)-ak. Starting from phase 0 with all k digits one, the overflow returns to phase 0 with k+1 zeros after three inner fills and four overflows:
- 0LE: 198·2^k + 20k - 46.
- 1RB: 186·2^k + 18k - 40.

The full return from phase 0 all zero width k to phase 0 all zero width k+1 includes the outer fill, giving the especially simple times 264·2^k - 112 and 248·2^k - 102 respectively. Every abstract transition has strictly positive cost. Every finite bit list either has an all-ones overflow or a normal carry, hence the phase language supplies unbounded live prefixes in every completion. No F0 query occurs.

The new generic Agent46PhaseCounterCheck.lean handles finite phase controllers with arbitrary phase frames, successor phases, extension words, and zero-inclusive symbolic carry lengths. Raw13Coupled6PhasedCounter.lean contains the twelve distinct concrete macros (two normal and four overflow for each table), plus exact seed and soundness statements. Source-level acceptance pending; do not count these leaves until the pinned CI run passes. The formal theorem proves nonhalting; the exact costs above follow from the checked macro costs and the elementary binary-fill recurrence.
