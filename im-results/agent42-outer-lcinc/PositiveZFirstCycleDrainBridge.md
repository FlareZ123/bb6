# Positive-z q4 first-cycle: exact counted-drain parameterization

**Status:** structural arithmetic match; not a TM2 transition proof.

The positive-z first-cycle observation in
`im-results/agent48-counted-inc0/Marker1TerminalQ4Macro.md` is

[
C_1(z)=6cdot4^{2^z-1}+42cdot2^{2^z-1}+12z+38.
]

The existing arbitrary-left S0 theorem
`s0Config_counted_drain_closed` in
`im-results/agent42-q4-s0-drain/S0CountedDrain.lean` proves

[
S_0(l,A,2^K-1,0,h)
longrightarrow
S_0(l,A,0,2^K-1,h)
]

in exactly

[
D(K)=6cdot4^K+42cdot2^K-12K-48
]

steps, assuming (2^K-1<2^A).

Set (K=2^z-1). Then

[
egin{aligned}
C_1(z)-D(K)
&=12(2^z-1)+12z+86\
&=12(2^z+z+6)+2.
end{aligned}
]

Thus the measured first-cycle cost is exactly consistent with a
source-level decomposition consisting of:

1. a q4 prefix/setup that reaches an S0 configuration whose binary
   counter is the all-ones value (2^K-1) at width (A), where
   (K=2^z-1);
2. the existing `s0Config_counted_drain_closed` theorem;
3. a remaining setup/postlude of (12(2^z+z+6)+2) steps.

This clarifies the notation in the empirical macro note: the
`drainCost(2^z-1)` term is the all-ones drain at **width**
(K=2^z-1), whose actual binary value is (2^K-1). It is not the
drain of the binary value (2^z-1).

## Distinguish the pre-checkpoint prefix

The first q4 checkpoint itself is reached at the empirically observed
time
`drainCost(z,0) + drainCost(2^z-1,0) + 12*(A+L+z) + 107`,
as detailed in `PositiveZCheckpointNormalForm.md`. That is a
**pre-checkpoint** two-drain candidate and should not be conflated with
the **post-checkpoint first-cycle** all-ones drain of width
`K=2^z-1` and actual value `2^K-1` analyzed above. The exact
intermediate configurations for both decompositions remain open.


The arithmetic identity is exact, but the decomposition remains a
hypothesis. The q4 checkpoint's right-side nested counter has not yet
been identified as the required S0 all-ones input, and the prefix,
head-coordinate, residual-left-context, and postlude equalities remain
unproved. The positive-z event-count formula is a separate open claim.
The authentic root endpoint has (z=2^b-1ge3), so the z=0 terminal
law is not applicable.

The root-side candidate canonical endpoint is developed separately in
`OuterLCIncCanonicalEndpoint.lean`; that entire module is also still
uncompiled.
