# Marker-1 S0 first-q4-checkpoint normal form: expanded simulation evidence

**Status:** reproducible computational evidence and a candidate cost decomposition; no Lean proof of this checkpoint macro.

The new self-contained simulator
`marker1_q4_checkpoint_sweep.js` transcribes the TM2 transition table and
initial tape convention from
`im-results/agent48-counted-inc0/marker1_terminal_q4_checkpoint.py`.
The experiment detects the first state-4, head-1 checkpoint of

[
S_0(ell,A,z,0,h),qquad
ell=	ext{markerWord}(1)++d0++d1pow(L)++lh.
]

At that checkpoint, all tested cases had the following left-facing word:

[
[0,1,1]++operatorname{binDec}(A+L+2,M-1)++LH,
qquad
M=2^A(2^{L+2}-1).
]

The right-facing suffix from the checkpoint head is exactly

[
0^3,1^{3z+5},0^2,1^{3cdot2^z},0^4,
]

with no further nonblank cells. The number of state-4/read-0 events up to
the checkpoint is

[
E_{mathrm{prefix}}(z)=3cdot2^z+3z+5,
]

equal to the total number of ones in those two right-hand runs.

## Observed data

For (A=4,L=2):

| (z) | first checkpoint step | q4 events | right suffix |
|---:|---:|---:|---|
| 0 | 179 | 8 | (0^3 1^5 0^2 1^3 0^4) |
| 1 | 287 | 14 | (0^3 1^8 0^2 1^6 0^4) |
| 2 | 515 | 23 | (0^3 1^{11} 0^2 1^{12} 0^4) |
| 3 | 1,043 | 38 | (0^3 1^{14} 0^2 1^{24} 0^4) |
| 4 | 2,639 | 65 | (0^3 1^{17} 0^2 1^{48} 0^4) |
| 5 | 8,015 | 116 | (0^3 1^{20} 0^2 1^{96} 0^4) |
| 6 | 27,911 | 215 | (0^3 1^{23} 0^2 1^{192} 0^4) |
| 7 | 104,447 | 410 | (0^3 1^{26} 0^2 1^{384} 0^4) |
| 8 | 404,903 | 797 | (0^3 1^{29} 0^2 1^{768} 0^4) |
| 9 | 1,595,447 | 1,568 | (0^3 1^{32} 0^2 1^{1536} 0^4) |

The left-word equality, right suffix, and absence of further ones also
passed for (A=3,L=2,z=0,ldots,5) and (A=5,L=4,z=0,ldots,5).

## Exact cost identity suggested by the data

Let (D(n)=operatorname{drainCost}(n,0)), using the existing recursive
function from `CountedReset.lean`. In every tested case, the first
checkpoint time is

[
T_{mathrm{prefix}}(A,L,z)
=D(z)+D(2^z-1)+12(A+L+z)+107.
]

For example, with (A=4,L=2), the formula gives the table above for
(z=0,ldots,9). The (z=0) specialization is the already checked
[
107+12(A+L).
]

The formula is consistent with a two-drain decomposition:
1. drain the initial binary value (z), costing (D(z));
2. drain an all-ones binary value (2^z-1) of width (z), costing
   (D(2^z-1));
3. pay a remaining linear bridge/postlude of (12(A+L+z)+107).

The observed right runs (1^{3z+5}) and (1^{3cdot2^z}) are consistent
with these successive unary counts, but the exact intermediate TM2
configurations have not been identified or proved. This decomposition
must therefore be treated as a hypothesis, not as a source theorem.

The separate first q4 cycle *after* this checkpoint has the still deeper
counted-drain parameterization in
`PositiveZFirstCycleDrainBridge.md`: with (K=2^z-1), its observed
cost matches an all-ones drain of width (K), actual value (2^K-1),
plus a further linear overhead. Its event-count formula is also still
unproved.

The experiment is reproducible with:

```sh
node marker1_q4_checkpoint_sweep.js 4 2 9 3000000
```

The simulator's checks are computational only. A formal proof still needs
to expose the intermediate S0 configurations and compose the existing
`s0Config_counted_drain_closed` theorem with the intervening TM2 frames.
