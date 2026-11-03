# Stronger finite-residue quotient obstruction: independent proof proposal

Agent 30, 2026-11-03. **Mathematical derivation, not yet Lean checked**; R007 follow-up beyond the already verified affine-modular theorem. This file should remain in `im-results/` pending a source-connected proof and independent check.

Let `H(z)=r*floor(z/2)+c+s*(z%2)` with odd `r`, `r≤2s`, and let `F_t=H^[t]`, `t≥1`. Define `δ=2s-r`. For any **positive** modulus `m`, conjectured stronger statement:

`(∀x y, x%m=y%m → F_t(x)%m=F_t(y)%m) ↔ m∣δ`.

This asks only that the positive iterate descend to *some* deterministic function on residue classes modulo m. The induced function may be nonlinear and entirely unrestricted.

The reverse implication is immediate from the kernel-certified quotient theorem `iterH_affine_modulus_iff_gap`: if m divides δ, every F_t has an affine formula modulo m, hence respects input congruence. The forward direction is derived below from a few points using the already source-checked exact dyadic translation and curvature identities.

## Necessity when m is even

Write `m=2k` with `k>0`, and `q=r^t` (odd). The exact translation identity `F_t(z+2^t*d)=F_t(z)+q*d` gives

`F_t(2^t*k)=F_t(0)+q*k`.

The two inputs `0` and `2^t*k=m*2^(t-1)` are congruent modulo m. If F_t respected residues, then `2k∣q*k`; cancelling the positive k forces `2∣q`, contradicting odd q. Hence no positive even modulus can carry such a deterministic quotient for any positive iterate.

## Necessity when m is odd

Write `m=2k+1`, `w=k+1=(m+1)/2`, `p=2^(t-1)`, `q=r^t`, `A=F_t(0)`. The shift identity gives

`F_t(2p)=A+q`, and `F_t((m+1)*p)=F_t(2p*w)=A+q*w`.

The inputs `p` and `(m+1)*p=p+m*p` are congruent modulo m, so quotient compatibility implies `F_t(p)≡A+q*w (mod m)`. Doubling yields

`2F_t(p)≡2A+q*(m+1)≡2A+q≡F_t(0)+F_t(2p) (mod m)`.

The separately proved exact dyadic curvature identity states that the two sides of this final congruence differ in `Nat` by precisely δ, in one order or the other. Consequently `m∣δ`. This completes the elementary argument and avoids modular inverses, unbounded enumeration, and assumptions about a particular trajectory.

**Machine B instance:** (r,c,s)=(3,4,5), δ=7, so a deterministic finite scalar residue quotient of ANY fixed positive iterate would exist only for m=1 or m=7. This is stronger than the already verified affine-modular classification because it excludes nonlinear lookup-table quotients as well.

## Independent finite falsification screen

A fresh Python simulator (outside Lean) checked all 17,856 parameter combinations with odd `r∈{1,3,5,7,9,11}`, `s` among eight consecutive integers starting at `ceil(r/2)`, `c∈{0,1,2}`, `t∈{1,2,3,4}`, and `1≤m≤31`. For each combination, it evaluated residue-compatibility on every input `0≤z<m*2^(t+2)`. **All 17,856 tests agreed** with `m∣2s-r`, and no counterexample was found. This is finite falsification evidence only; the preceding argument supplies the all-integer derivation. The stronger statement awaits independent scrutiny and Lean kernel verification.
