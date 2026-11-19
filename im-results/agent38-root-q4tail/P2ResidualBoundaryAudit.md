# P2 q4Tail residual boundary: correction to the proposed S0 input

**Status:** exact source-coordinate audit of the existing prefix definitions; not a Lean-compiled theorem. This is a countercheck of the proposed frame identity, not a new BB(6) result.

## Claim

The proposed target in `im-results/agent44-p2-postlude/S0DrainQ4Postlude.lean`,
`s0Config (p2ResidualLeft m tail) (n-1) (2^(n-1)-1) 0 H), cannot be the
output of the current `secondCyclePrefix_from_checkpoint` at the authentic
second checkpoint (h=1) with the stated
`p2ResidualLeft = 1^(m+2) ++ 0100 ++ tail).

The residual actually begins
`1^(m+2) ++ 0101 ++ 1^7 ++ ...` (the seven-one tail prefix is more than
needed to refute the proposed `tail=100` guard). In particular, the
proposed fourth boundary bit is false in the target but true in the actual
q4Tail output.

## Coordinates

Use the existing definitions:
- checkpoint head (h=1);
- (m=3\cdot2^z+3z+7);
- (n=2^{2^z-1}\ge2);
- (h_1=h+4+m=m+5) (start of the two-zero setup);
- (h_2=h_1+2=m+7) (start of the state-1 block scan);
- (g=h_2+3n=m+7+3n);
- q4Tail output head (H=g-5=m+2+3n);
- (a=n-1).

The left S0 counter `binDec a (2^a-1)=d0pow a` has length (3a=3(n-1)).
Consequently its residual left context begins at
[
H-3a=m+5.
]
Thus residual index (j) is the actual tape cell (m+5-j).

## Exact bits

The two-zero setup writes cells (m+5,m+6) to one. The E-scan consumes
the (m) ones at cells (5,ldots,m+4). The 34-step bridge output is
`secondCyclePrefix34End = <4,4,[-7,-6,-5,-2,1,3]>` relative to (h).
Its marked cells are ones; unmarked cells retain the input. Together with
the established input window, this gives:
- cell (4=h+3): one (marked at offset (+3));
- cell (3=h+2): zero (unmarked; input zero);
- cell (2=h+1): one (marked at offset (+1));
- cell (1=h): zero (unmarked; input zero);
- cell (0=h-1): one (unmarked; input one).

The last five facts are unchanged by the later two-zero setup, block scan,
and q4Tail: all those operations are to the right of cell (0); for
(z\ge1), (h_2\ge23) and (g-4\ge25), so cell (0) is outside both
the d0 sweep interval and q4Tail frame.

Therefore the residual bits at indices (0,ldots,m+5) are:
- indices (0,ldots,m+1): all one (the first setup cell, the (m)-cell
  E-scan run, and cell (4));
- indices (m+2,m+3,m+4,m+5): (0,1,0,1), from cells (3,2,1,0).

So the actual residual prefix is
[
1^{m+2}\;0101,
]
not (1^{m+2}\;0100). In addition, the next three cells
(-1,-2,-3) are all one, so the tail after this (0101) begins (111),
not (100).

## Consequence and next step

The exact target equality required by `p2S0Drain_q4Postlude` and the
`ht0/ht1/ht2` assumptions of `p2PostludeFrame_typeAWindow` is not
established by the current second-cycle prefix; its displayed residual
contract conflicts with the unchanged source bit at cell (h-1=0).

Please do not compose the P2 postlude theorem with the current q4Tail
frame on the basis of the (0100)/(100) claim. Re-derive the q4Tail
left-frame factorization and the appropriate next macro from the actual
(0101) boundary, or find a different source transition that changes
cell (0) before the S0 handoff. The original q4Tail prefix remains
valid; this audit only rejects the proposed frame-to-S0 interface.

Relevant source facts:
- `PositiveZSecondCyclePrefix.lean`: (h_1,h_2,g), and the exact
  q4Tail output composition;
- `PositiveZSecondCycleBridge.lean`: input window and
  `secondCyclePrefix34End`;
- `PositiveZFirstCycleBridges.lean`: `afterFirstCycleTwoZero`
  writes only (h_1,h_1+1);
- `Q4Suffix.lean`: q4Tail frame support and endpoint;
- `S0DrainQ4Postlude.lean`: the incompatible (0100) / (100) target.
