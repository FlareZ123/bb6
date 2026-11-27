# Raw13 E1=1LB nested binary counters

Two previously unresolved one-hole residuals are:

- 1RB1LD1RC0RF1LA1RE1LA0LA---1LB0LC0RB
- 1RB1LD1RC0RF1LA1RE1LA0LA---1LB0LD0RB

Both have a single unassigned row E0. Their only difference is F0, which writes zero and moves left to either C or D. Both C0 and D0 write one and move left to A; all macro uses of F0 are followed by a zero read. The same exact macro identities therefore work for both tables.

## Exact return map

For head-relative zipper words, write A(l,r) with l including the scanned cell, both nearest-first; A([],r) scans implicit blank. Set U=11, Z=00, T=10. The root family is

    R(k,m) = A([], U^k 0 U^(m+1) 0).

The exact positive-step return is

    R(k,m) -> R(k+1,m+2^k).

In particular at step 31 the blank run reaches R(1,1), and the subsequent root with k leading pairs has exactly 2^(k+1) trailing ones. The machine never queries E0. This is an unbounded inductive proof, not a conjecture about the asymptotic orbit.

### Mechanism

The rightward B/F sweep erases pairs of ones into pairs of zeros; the leftward A/D sweep consumes 10 and emits 11. Two independent binary encodings use least-significant bits first: I-encoding b -> 0b and O-encoding b -> b0. Define

    I(w,L) = A(0 encI(w) 1 L, 1110)
    O(w,m) = A(encO(w) 1, 0 U^(m+1) 0).

A local reset is exact for any tail L:

    A(0L,U^(s+1)10) -> A(Z^s 1 L,1110), cost 2s+12.

Using the reset and a leftward pair sweep gives the inner increment

    I(1^j 0 w,L) -> I(0^j 1 w,L)

in 4j+28 steps. For all-one inner bits, the overflow instead gives

    I(1^j,L) -> A(L,0 U^(j+2) 0), cost 14+2j.

An induction on j fills any j-bit all-zero low prefix to the all-one prefix, preserving all higher bits. The initial right word 111 (rather than 1110) is harmless: the exact four-step prefixes merge. Hence a newly initialized inner counter finishes regardless of its length.

The marker initialization transforms A(0L,U^k 0 U^(m+1)0) to A(0 encI(0^m) 1 Z^k 1 L,111) in 2k+2m+10 steps. The only E transition is E1. The inner completion turns this into the outer configuration with the same preserved outer tail. With a low prefix of j ones, the outer counter first sweeps those pairs off the left, then uses the marker initialization and entire inner enumeration to obtain

    O(1^j 0 w,m) -> O(0^j 1 w,m+1).

The outer fill induction gives a change of m by c(k), where c(0)=0 and c(k+1)=2c(k)+1; hence c(k)=2^k-1. The initial inner completion adds one to m, and the final outer overflow maps O(1^k,m') to R(k+1,m') in 2k+2 steps. This proves the root return for every k,m, with a strictly positive cost.

## Formal proof and coverage

[Raw13Coupled6Nested1LB.lean](Raw13Coupled6Nested1LB.lean) proves the sweep identities, inner/outer carries and all-prefix fill by induction, exact overflow and root growth, then transports via never_of_growth to every compatible completion. The core rootGrowth and familyGrowth were checked in Lean 4.36.0-rc2 against copied zipper semantics, with only propext and Quot.sound; full source check target coupled6Nested dispatched at b522775f7cf1bb79706edd0d87bd4d5371586e81. The source never theorem uses Classical.choose only to select a positive finite cost from the proved existence statement, not to postulate behavior.

These are the last two unresolved E1=1LB residuals after the [two exact late queries](Raw13Coupled6Late1LB.md) and four extra BiDFA witnesses. The canonical sibling generator has been updated to graft all four new proofs without naive multi-million-step trace expansion. Its source-complete sibling run is pending; the proposed conservative weighted bound is 2,651,340. No other sibling or global BB6 closure follows from this alone.
