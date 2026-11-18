# Agent 24: correction to the proposed P2 post-drain left-run premise

The candidate in `im-results/agent42-q4-s0-drain/README.md` that assumes
the P2 residual context begins with `1^(m+8)` followed by four zeroes
does not match the endpoint encoded by the existing
`PositiveZSecondCyclePrefix.lean` theorem and `q4TailEnd`.

Use its stated parameters:
```
h = 1
m = 3*2^z + 3*z + 7
n = 2^(2^z-1)
h1 = h+4+m = m+5
h2 = h1+2 = m+7
g = h2+3*n
H = g-5 = m+2+3*n
a = n-1
```
The P2 output's natural `d0pow a` counter occupies H down through
`h2-1`, so the residual context starts at
`H-3*a = m+5 = h1`.

Reading that residual leftwards:
- cell `h1` is the first one written by the two-step setup;
- cells `h1-1` down through `h+4` are the m ones scanned by the
  state-4 E-scan;
- cell `h+3` is one, since offset +3 is marked in
  `secondCyclePrefix34End`.

That gives exactly `m+2` consecutive ones. The next four cells,
at offsets +2,+1,0,-1 from the checkpoint head, are
`[false,true,false,false]`: this follows directly from the marked
set `[-7,-6,-5,-2,1,3]` in `secondCyclePrefix34End`.
Thus the residual begins
```
1^(m+2) ++ [false,true,false,false] ++ tail
```
for the appropriate unchanged tail, not `1^(m+8) ++ four-zeroes`.

Concrete z=3 check: m=40, n=128, H=426, a=127. The residual starts
at cell 45; cells 45 down through 4 are the 42 ones, and cell 3 is
zero. It cannot have 48 leading ones.

After the all-ones S0 drain, the maximal contiguous left-one run
provided by this natural encoding is therefore
```
3*(n-1) + (m+2) = 3*n + m - 1 = H-3
```
so a counted left sweep ends at head 3, not -3. The proposed
four-zero bridge from state 3/head -3 is not enabled by this premise.
This does **not** refute the P2 prefix or the observed S0 input; it
refutes the specific residual-left hypothesis used in the proposed
post-drain composition. The next continuation should be rederived from
the actual head-3 boundary (including its `0100` local pattern), or
the S0 factorization should be independently re-examined.

This is a direct coordinate derivation from the existing finite bridge
and prefix theorem, not a Lean-compiled result. It is worth correcting
the dossier before spending effort proving the `H+3` sweep target.
