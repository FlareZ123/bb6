# Agent 24: P2 → q4/S0 postlude → P22 is a complete next-checkpoint composition

The P2 correction has a stronger consequence than merely rejecting the
head -3 zero4 bridge. Assuming the existing P2 prefix theorem's input
conditions and its natural S0 encoding, the generic
`q4S0Postlude_at` applies after the counted drain and produces the
exact input frame for the 22-step prefix again.

For P2 let
```
m = 3*2^z + 3*z + 7
n = 2^(2^z-1)
a = n-1
H = m+2+3*n
ell = 1^(m+2) ++ [0,1,0,0] ++ tail
```
The counted drain output has left-facing stream `d1pow a ++ ell`.
The first `K=3*a+m+2=H-3` cells are one, and the right sentinel
at H+1 is zero. The counted left sweep therefore ends at head 3.
The four cells 0..3 are unchanged and, from the displayed residual
pattern, are exactly `[0,0,1,0]`. This is the existing
`q4S0Final4Input`; hence `q4S0Postlude_at K T H` gives a
`3*K+4=3*H-5` source run to state 4 at head 1.

Crucially, this state-4 frame is the next 22-step checkpoint:
- P2's 34-step bridge leaves cells -3,-2,-1 equal to 0,0,1
  (the marked offsets -5,-6,-7 are farther left; offsets -4,-3,-2
  are 0,0,1 in physical order);
- the q4 final frame writes cell 0 to 1 and cells 1,2,3 to 0;
- the sweep boundary writes cell 4 to 0.
Thus the next head-1 window at offsets -4..3 is
`[0,0,1,1,0,0,0,0]`, exactly
`firstCyclePrefix22Start`.

Its right suffix is also exactly the 22-step prefix's parameterized
input:
```
0^3 ++ 1^H ++ 0^2 ++ 1^(3*2^a) ++ 0^4
```
The run of H ones is cells 5..H+4: the sweep sets 5..H+1,
and the original S0 right-facing word supplies H+2..H+4. The
two zero separators and the right unary counter are untouched.

Therefore the next prefix can be taken as
`firstCyclePrefix_from_checkpoint` with `m=H`,
`n=2^a`. The P2 postlude is not the proposed 0000/001001
far-right path; it reaches a valid type-A q4 checkpoint at head 1,
which then feeds P22. This gives an alternating prefix sequence:
A/P22 → Q → B/P34 → Q → A/P22 → Q → ...

This statement is still a source-level composition obligation: the
P2 endpoint `ell) identity and its first-cycle input composition
need explicit Lean proofs, and the output frame equality must be
kernel-checked. But the existing `q4S0Postlude_at` and
`firstCyclePrefix_from_checkpoint` interfaces are already the exact
macros needed. The earlier `m+8`/head -3 premise should not be used
for the natural P2 width `a=n-1`.
