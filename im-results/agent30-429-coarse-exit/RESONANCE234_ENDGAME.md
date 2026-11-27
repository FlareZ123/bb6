# d=234 resonance endgame (Agent 30, 2026-11-27)

Status: intermediate.  The algebra below is encoded in the neighboring Lean
modules and is being checked by the dedicated manual CI workflow.  Do not
promote this note to `results/` until the full source dependency chain is green.

## Exact first resonance

For total scale `m>=2` the first nonzero first-burst Cantor resonance
`d=234` reaches

[
p_m=(416m+3965,;72,16^m-808m-7677)
]

after `8m+7` accelerator transitions from `prepared m 234`.  Therefore

[
U(p_m)=2496m+23808,qquad
V(p_m)=216,16^m+72m+759.
]

The 12-step tail from the preceding low phase has branch word

`Oe F Oo F Oe F F F Oe F F F`.

## Second resonance: parity split

For an exact second burst with leading V coefficient `27*4^I`, a surviving
resonance forces
[
2496m+23808=18+54B,
]
hence `m=2 (mod 9)` and, for `m=9q+2`, `B=416q+533`.

For the doubled leading scale `54*4^I`, four bounded coefficient steps leave
only normalized values `0` and `36`.  The physical zero alternative is
excluded exactly as in the original negative-error theorem, so the only
resonance is
[
2496m+23808=36+108B.
]
Consequently `m=8 (mod 9)`, and for `m=9q+8`,
[
B=208q+405.
]

The large-scale theorem `d234_large_non8` uses this to close every
`m>=16` outside `8 mod 9`.

## Universal first-resonance slope

If the first resonance is
[
d=18+216,mathrm{word4}(
eg e,2s),
]
then the outer low-cycle slope `A` of the transformed U error satisfies
[
3A_{m post}=32d.
]
The preceding branch word cancels completely.  For `d=234`, the slope is
`2496`.

## Minimal doubled resonance

Let a doubled-scale resonance word have minimal length `i`, so its first
temporal base-four digit is 1.  Put
[
H=4^i,qquad
B=mathrm{word4}(e,i),qquad
9B=208m+1981.
]
At the start of the ordinary blocks the V-error is
[
y=108m+777-18i.
]

For arbitrary branch words the low-order errors `x,z` satisfy
[
y+18ile zle y+42i,
]
[
(-2(y+42i)+6)Ble xle(-2y+54)B.
]
Minimality gives `H<=4B`, while the universal word bound gives
`3B+1<=H`.  For `i>=7` the elementary bound `500i<=4^(i-1)<=B`
is enough to deduce `m>=5i+61`.

Define
[
Delta=-6x+4z+12.
]
The coarse inequalities already imply
[
54H^2<16Delta,qquad 4Deltale27H^2.
]
No detailed digit statistic is needed.

At the physical resonance endpoint write `z=3q`.  If `d_0` is the
deviation after the two-step false-phase rotation, then
[
3d_0=Delta.
]
With
[
J=m-i+1,quad N=16^{m-i},quad X=16^m,quad D=d_0,16^J,
]
the band becomes
[
18X+Nle Dle36X.
]
The four-step low-cycle invariant is
[
C=72X+q-2+24J.
]
The V-error bound and `m>=5i+61` give
[
72Xle Cle72X+4N+27.
]
Hence
[
Dle36X,quad Cle4D+27,quad 8D+21le5C.
]
Those are precisely the hypotheses of `phase_cycles_direct_return`: after
`J` exact low cycles the state lies in the immediate `F,E-even` return
strip.

The transformed-to-physical cancellation is especially simple:
[
3u_0+d_0 = 72X+q-2,
]
so the U-error disappears from the cycle invariant.

## Short minimal resonance

A base-four 0/1 word has only 16 possible residues modulo 256.  Combining that
with `i<=6` and `9B=208m+1981` forces the unique short resonance
[
m=35,quad B=1029=(100011)_4.
]
The exact accelerator witness is
[
mathrm{run};559;(mathrm{prepared};35;234)
=(0,;100353353393387804136910732226917626776914176).
]

## Remaining composition

The only missing composition step is mechanical rather than a new asymptotic
idea.  A nonminimal resonant word begins with one or more false blocks.  Each
leading false block is exactly FF at transformed level and sends
[
(P,I,y)mapsto(4P,I-1,y+18),
]
preserving
[
y=108m+777-18I
]
and strictly improving the separation budget.  Strip those blocks until the
first true digit.  The minimal suffix is either the finite `m=35` case or
has length at least 7 and enters the scalar window above.  The neighboring
`BB429ResonanceShift.lean`, `BB429ResonanceMinimal.lean`,
`BB429ResonancePhysical.lean`, and `BB429ResonanceTail.lean` formalize the
pieces needed for that final composition.
