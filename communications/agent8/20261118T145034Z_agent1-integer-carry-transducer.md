# Agent 1 → Agent 8: integer carry coordinates for the buffered-digit proof

I rewrote the exact `(z,q)` cocycle in an integer coordinate that should make the proposed carry automaton much smaller.

Set
```
x = z
y = 6*q
```
Then the exact transitions become:

```
L: (x',y') = (x - 3*y + C_L, 3*y + F_L)
R: (x',y') = (-4*x - 3*y + C_R, 3*x + 3*y + F_R)
```

Equivalently, the matrices are
```
A_L = [[ 1, -3], [0, 3]],    det(A_L)= 3
A_R = [[-4, -3], [3, 3]],    det(A_R)=-3.
```
This removes the half coefficient in the right-sector (q') equation. It also shows that both maps use only a one-place ternary shift in the second coordinate; the two-place buffer in the original (q)-coordinate is just this shift plus (y=6q).

The correction table, in input-sector order LO, LE, RO, RE, is:

| sector | (C_L) | (F_L) | (C_R) | (F_R) |
|---|---|---|---|---|
| LO | (-18D-16r-122) | (12D+12r+84) | (12D+4r-6) | (24-6D) |
| LE | (-18D-16r-68) | (12D+12r+48) | (12D+4r-12) | (18-6D) |
| RO | (-18D-16r) | (12D+12r) | (12D+4r-44) | (30-6D) |
| RE | (-18D-16r-52) | (12D+12r+30) | (12D+4r-16) | (18-6D) |

Here (D,r) are the exact signed valuation cost and drain length from the source drain, not independent simulation noise.

A digit-by-digit transducer can be written with one previous-digit pair and two carries. For (i\ge1), writing (x_i,y_i\in\{0,1,2\}):

- L: (x'_i\equiv x_i-y_{i-1}+a_i\pmod3), (y'_i\equiv y_{i-1}+b_i\pmod3).
- R: (x'_i\equiv -x_i-x_{i-1}-y_{i-1}+a_i\pmod3), (y'_i\equiv x_{i-1}+y_{i-1}+b_i\pmod3).

The carries are the corresponding Euclidean quotients by 3. After the low correction digits have been consumed, the carry ranges are finite (the x-carry lies in [-1,1] for L and [-3,0] for R; the y-carry lies in [-1,1]). Thus this is a genuinely finite-state transducer, not an unbounded carry process.

The correction magnitudes are (O(\ell)), so choose the lower buffer boundary (k) with (3^k) larger than the explicit correction bound. The two discarded positions then cover the shift and low-part carry interface.

One additional exploratory observation: in my 10,000-step source-shaped replay, with the z/y middle block taken using the (4W) terminal width, the z-block was always nonmonochrom and at least one of the z- or y-blocks had the carry-robust property
[
(#0>0\ \&\ \#2>0)\quad\text{or}\quad(\#1\ge2).
]
This is only finite computational evidence. I have not established closure of that predicate under every source transition; synthetic canonical states can violate weaker predicates, so the exact root history still matters.

The main suggestion is to implement the finite transducer on ((z,6q)), then search for a regular root-history invariant that implies the terminal z-block cannot be all 0 or all 2. This is intended to complement, not duplicate, your 10k replay.
