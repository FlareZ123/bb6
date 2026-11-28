# Raw13 coupled-six E1=1RA: nested binary carry

**Status:** local original-semantics Lean 4.36.0-rc2 proof against recovered accepted dependency objects (artifact 15220979453, run 46037817669). This is an intermediate exact reduction, not a proof of nonhalting or parent coverage.

The literal is `1RB1LD1RC0RB1LA1RE1LC0LA0RF1RA---0LC`; F0 is the unassigned transition. State A zipper `A(L,R)` has the scanned cell at the head of L, right tape nearest-first, implicit zeros beyond the ends. Define D0=0101, D1=0110, little-endian digit words, U=011, V=1. The authentic 29-step seed is A([],111 D1 U).

## Checked rules

For arbitrary protected L,R and k,j>=0:

- Carry: A(0L,1^k D1^j D0 R) -> A(0^k 1 L,D0^j D1 R), exactly k+8j+8 assigned steps.
- U overflow: A(0L,1^k D1^j U) -> A(1 0^k 1 L,D0^(j+1) V), exactly k+8j+11.
- V overflow, at least one D1: A(0L,1^k D1^(j+1) V) -> A(0^k 1 L,D0^(j+1) U), exactly k+8(j+1)+10.
- Left normalization: 11X -> X with 01 prepended to R (2 steps); 100X -> X with 111 prepended to R (3 steps); 101X -> 111X without modifying R (4 steps).

These rules are proved in [Raw13Coupled6OneRACarry.lean](Raw13Coupled6OneRACarry.lean). The first three audited axioms are [propext, Quot.sound]; seed and blank_left are [propext].

## Exponential acceleration

[Raw13Coupled6OneRAAdvance.lean](Raw13Coupled6OneRAAdvance.lean) defines a successful ordinary binary increment relation on fixed-width bit lists and its n-fold iteration. For any protected L,R and any successful sequence of the stated number of ordinary increments w -> w':

- Drain(k): A(0^(3k)L, digits(w)R) -> A(L,1^(3k) digits(w')R), with 2^k-1 increments.
- Fill(k): A(0L,1^(3k) digits(w)R) -> A(1L,1^(3k) digits(w')R), with 2^k increments and positive primitive cost.
- Blank advance: A([],1^(3k) digits(w)R) -> A([],1^(3(k+1)) digits(w')R), with 2^k increments and positive primitive cost.

Proof: Fill(k) is one carry followed by Drain(k). Drain(0) is identity. Drain(k+1) uses Drain(k) on a protected 000L suffix, then Fill(k) on 00L, then the three-step 100 rewrite. The increment counts add to 2^(k+1)-1. The final blank-left return uses the virtual-zero triple rewrite.

All three exported acceleration theorems compile and audit [propext, Quot.sound], without sorry or native_decide. These are universally quantified original machine transitions, not numerical extrapolations. Reproduce by placing both sources next to the recovered SweepPumping and its dependency objects, compiling Carry with -o first, then Advance, using the artifact directory as LEAN_PATH.

## Remaining obstacle

The U overflow introduces an extra left marker and can break the alignment required by the ordinary increment macro. The authentic orbit reaches overflows, so the conditional blank advance alone cannot establish infinite growth. The required next step is a closed cross-overflow stack/digit grammar, or a sufficiently strong invariant on the resulting larger return map. No NeverHalts theorem, full-source CI acceptance, parent Cover, or canonical reduction is claimed.
