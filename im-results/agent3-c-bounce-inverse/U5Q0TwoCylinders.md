# U5 q=0 secondary fan: two excluded 2-adic cylinders

**Status:** exact algebraic reductions and Lean proof drafts exist; exact local preflight and CI are still pending. These are two infinite subfamilies, not a closure of the entire (w\equiv1\pmod{16}) cylinder.

## Common source-parent setup

For (t=39+64h), the q=0 U5 branch reaches the odd/odd target
[
X_t=(44t-1,42t-1).
]
Its odd/odd low-value inverse has the unique parent
[
P_0(h)=\left(1674+2752h,\;1654+2720h\right).
]
The sum is (8S), where (S=416+684h).

The exact secondary parent fan in [Agent 11's `U5Q0SecondaryFan.lean`](../agent11-c-low58/U5Q0SecondaryFan.lean) reduces reachability of (P_0(h)) to:
- a direct alternative (E_h=(1036+1708h,1966+3242h)); or
- a bounce alternative (B_{r,h}=(2q-2,2487+4096h-q-3r)), with (r\ge1) and (4^r q=S).

The zero-left branch is already excluded by the imported source lemma. The two cylinders below eliminate every direct/bounce alternative.

## Cylinder A: (h=16+32u)

Here
[
S=416+684(16+32u)=32(355+684u),
]
and the factor in parentheses is odd. Hence (S\equiv32\pmod{64}), so (4^r q=S), (r\ge1), forces (r=1) or (r=2).

| Parent alternative | Exact forced inverse path | Forbidden terminal |
|---|---|---|
| (E_h) | Four even-right inverses | ((129298+249176u,3363+6484u)), odd right, sum (1\bmod4) |
| (B_{1,h}) | One even-right inverse | ((70856+136544u,32589+62800u)), odd right, sum (1\bmod4) |
| (B_{2,h}) | No further inverse needed | ((1418+2736u,67307+129704u)), odd right, sum (1\bmod4) |

The terminal states are excluded by the existing blank-image theorem for odd right counter and coordinate sum (1\bmod4).

Proof draft: [`U5Q0SecondaryH16.lean`](U5Q0SecondaryH16.lean).

The residual identity
[
211t+1360+22155w=20\cdot2^{201+3360w}
]
implies (t\equiv1063\pmod{2048}) whenever (w\equiv1\pmod{2048}). Thus
[
t=39+64(16+32u)
]
for some (u\ge0), and the q=0 terminal parent is excluded.

Root-composition draft: [`U5Q0W1HighStop.lean`](U5Q0W1HighStop.lean).

## Cylinder B: (h=40+128u)

Here
[
S=416+684(40+128u)=128(217+684u),
]
with odd factor, so (S\equiv128\pmod{256}). Therefore (4^r q=S), (r\ge1), forces (r=1,2,3).

| Parent alternative | Exact forced inverse path | Forbidden terminal |
|---|---|---|
| (E_h) | Six even-right inverses | ((328514+1035608u,2055+6484u)), odd right, sum (1\bmod4) |
| (B_{1,h}) | One even-right inverse | ((173264+546176u,79689+251200u)), odd right, sum (1\bmod4) |
| (B_{2,h}) | One even/odd seven-sector inverse, then one affine even-right inverse | ((208327+656728u,62151+195924u)), odd right, sum (2\bmod4) |
| (B_{3,h}) | One even-right inverse | ((166748+525656u,82941+261460u)), odd right, sum (1\bmod4) |

The (B_2) terminal is excluded by the corresponding odd-right, sum (2\bmod4) blank-image theorem; the others use sum (1\bmod4).

Proof draft: [`U5Q0SecondaryH40.lean`](U5Q0SecondaryH40.lean).

The residual identity implies (t\equiv2599\pmod{8192}) whenever (w\equiv4609\pmod{8192}), so
[
t=39+64(40+128u).
]
This excludes the q=0 terminal parent on that root cylinder.

Root-composition draft: [`U5Q0W4609HighStop.lean`](U5Q0W4609HighStop.lean).

## Root-level composition

Both high-stop files reuse the same already-developed exact chain:

[
\text{q=0 parent excluded}
\Longrightarrow \text{y=3 residual terminal excluded}
\Longrightarrow B_s\text{ excluded}
\Longrightarrow A_s\text{ excluded}
\Longrightarrow \text{authentic high-stop root excluded}.
]

The y=3 parent fan is split into q=0, q=1, and q\ge2:
- q=0 is eliminated by the new cylinder-specific parent theorem;
- q=1 is eliminated by the odd-right sum-two invariant;
- q\ge2 contradicts the residual parameter's (1\bmod8) residue.

The existing residual nonvacuity and strict-monotonicity lemmas provide infinitely many distinct root indices in each cylinder.

## Remaining work

1. Exact local Lean 4.36.0-rc2 preflight for all four new files against the actual source closure.
2. Confirm every `#print axioms` output has no `sorryAx` or custom axioms.
3. Only then run targeted CI and promote a polished theorem into `results/`.
4. Continue beyond these two cylinders: they do not settle arbitrary (h), and do not determine BB(6).


## Combined root-residue view

The two proven-in-draft root cylinders are disjoint. Modulo 8192 their union is
[
w\equiv 1,2049,4097,4609,6145\pmod{8192}.
]
The first four residues are exactly (w\equiv1\pmod{2048}); the fifth is (w\equiv4609\pmod{8192}). This is only the union of the two constructed families; no conclusion is asserted for the other eleven lifts of w=1 mod 512 among the 16 residue classes modulo 8192 or for arbitrary (w).


## Nearby unresolved branch: h=8+128u

A diagnostic reduction of the same secondary fan shows that, on (h=8+128u), (E_h) and (B_{1,h}) already reduce to odd-right sum-one forbidden states. The remaining alternatives are:

- (B_{2,h}=(734+10944u,34881+518816u)), even/odd with coordinate sum (3\pmod4) and (15\pmod{16});
- (B_{3,h}=(182+2736u,35154+522920u)), even/even sum-zero with quotient (S_3=4417+65707u);
- (B_{4,h}=(44+684u,35220+523946u)), even/even sum-zero with quotient (S_4=4408+65578u).

The specialized even/even sum-zero parent theorem applies only when its quotient is nonzero mod four; the complete parent fan retains an unbounded secondary-depth branch when that condition fails. No closure is claimed here. This is the next nearby open branch, handed to Agent 11 for integration with its existing secondary-valuation work.


## Aggregate Lean audit root

`U5Q0TwoCylindersAudit.lean` imports the four new source proof modules plus the existing W1821 baseline and prints axioms for both secondary-parent closures, all three infinite root-family theorems, and all three pairwise-distinctness theorems. Compiling this one root against the repository's actual import closure forces all five modules to compile; it is an audit harness, not a result.


The two modular reductions have explicit integer witnesses:
[
211\cdot1063+1360+22155=121\cdot2048,
]
[
211\cdot2599+1360+22155\cdot4609=12532\cdot8192.
]
