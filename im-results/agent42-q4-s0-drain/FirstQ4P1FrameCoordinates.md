# First q4 checkpoint: pointwise frame-to-side coordinate derivation

**Status:** exact coordinate derivation from the current source definitions; not yet Lean-compiled. This is the remaining tape-identity proof target after `firstQ4Checkpoint_run`, not a new transition simulation or a BB(6) result.

## Target

Let
[
M=2^A(2^{L+2}-1),qquad
w=A+L+1,qquad
q=2^{A-1}(2^{L+2}-1)-1,
]
with (A>0), and let (T) be the second-drain tape
[
T=operatorname{s0Config}(operatorname{firstQ4Left2}(L,A),
z,0,2^z-1,3z+5).mathrm{tape}.
]
Put (h=3z+5), (k=3z+2), and
[
S=operatorname{s0LeftSweep}(k,T,h).
]
The actual first-checkpoint output in `firstQ4Checkpoint_run` is
[
C=operatorname{q4FrameAt}(S,3,
operatorname{q4S0Final4Inside},operatorname{q4S0Final4End}).
]

The desired exact source theorem is
[
C=langle 4,1,operatorname{firstCycleCheckpointTape}(z,w,q)angle.
]
The arithmetic/list side reparameterization is already formalized in
`FirstQ4P1Reparam.lean`. What remains is to prove that the actual
`q4FrameAt` tape has those two side lists.

## Sweep and final-frame coordinates

The existing `s0LeftSweep_shift` theorem gives, for every absolute cell (x),
[
S(x)=
egin{cases}
0,&x=4,\
1,&5le xle 3z+6,\
T(x),&	ext{otherwise}.
end{cases}
]
Here (h-k=3). The four-step q4 frame is at head 3 and writes
[
(C(0),C(1),C(2),C(3))=(1,0,0,0).
]
Outside those four cells, (C(x)=S(x)).

The S0 side-cell identities at the second-drain output are
[
T(h-i)=operatorname{sideBit}
  (operatorname{d1pow}(z)mathbin{++}operatorname{firstQ4Left2}(L,A),i),
]
and
[
T(h+1+j)=operatorname{sideBit}
  (operatorname{s0RightFacing}(2^z-1),j),
]
where
[
operatorname{s0RightFacing}(2^z-1)
=[0,1,1,1,0,0]mathbin{++}operatorname{d1pow}(2^z).
]

## Left-facing output, from head 1

For (i=0,1), the frame gives (C(1-i)=0,1). For (i=2), the unchanged cell (C(-1)=T(-1)) is the third bit of the (d0) block in `firstQ4Left2`, hence 1.

For (ige3), the sweep and frame do not touch cell (1-i). Its S0 left-side index is
[
h-(1-i)=3z+4+i.
]
Removing the `d1pow z` prefix (length (3z)) and the
`markerWord 2 ++ d0` prefix (length 7) leaves index (i-3) in
[
operatorname{binDec}(A+L+2,M-1)mathbin{++}lh.
]
Therefore the output left-facing stream is exactly
[
[0,1,1]mathbin{++}
operatorname{binDec}(A+L+2,M-1)mathbin{++}lh.
]
Using `FirstQ4P1Reparam.firstQ4P1Left_eq_firstCycleCheckpointLeft`,
this is `firstCycleCheckpointLeft w q`.

## Right-facing output, from head 1

Index (i) denotes absolute cell (2+i). The cases are:

| Checkpoint-side index (i) | Absolute cell | Source of output bit | Value |
|---|---:|---|---:|
| (0,1) | (2,3) | final q4 frame | 0 |
| (2) | (4) | left sweep's cleared cell | 0 |
| (3le ile 3z+4) | (5ldots 3z+6) | left sweep | 1 |
| (3z+5le ile 3z+7) | (3z+7ldots3z+9) | S0 right-side indices (1,2,3) | 1 |
| (i=3z+8,3z+9) | (3z+10,3z+11) | S0 right-side indices (4,5) | 0 |
| (3z+10le i<3z+10+3cdot2^z) | (3z+12ldots) | `d1pow (2^z)` | 1 |
| (ige3z+10+3cdot2^z) | remaining cells | blank S0 suffix / four explicit zeros | 0 |

Thus the right-facing stream is exactly
[
[0,0,0]mathbin{++}1^{3z+5}
mathbin{++}[0,0]mathbin{++}operatorname{d1pow}(2^z)
mathbin{++}[0,0,0,0],
]
which is `firstCycleCheckpointRight z`.

## Formalization recipe

1. Define a local `firstQ4P1Output` by the exact RHS of
   `firstQ4Checkpoint_run`.
2. Reuse `q4FrameAt_tape` and specialize `s0LeftSweep_shift` to
   `x=4`, `5≤x≤3z+6`.
3. Prove left-cell equality by splitting (i=0,1,2) and (i≥3);
   use `s0Config_left_cell`, `d1pow_length`, and
   `sideBit_append_right` twice (prefix lengths (3z) and 7).
4. Prove right-cell equality by splitting at
   (3), (3z+5), (3z+8), (3z+10), and
   (3z+10+3cdot2^z); use `s0Config_right_cell`,
   `s0RightFacing`, and `sideBit_d1pow_true`.
5. Use a local fieldwise Config extensionality lemma. The repository's
   `Config` structure does not generate `Config.ext`; destruct both
   configurations, identify state/head, and use `funext` for tapes.

This closes the exact first-q4-frame-to-P1-input boundary once the
coordinate lemmas are compiled. It does not close the separate
`OuterLCIncCanonicalEndpoint` root equality, the later q4 cycles, or
any universal BB(6) upper bound.
