# U5 q=0 residual congruence: a mod-105 constraint on the secondary fan

**Status:** exact integer derivation from the residual identity; not yet Lean-compiled. This is an intermediate arithmetic constraint, not a reachability exclusion and not a BB(6) result.

## Hypotheses and the new congruence

Assume the U5 high-stop residual identity
\[
211t+1360+22155w=20\cdot 2^{201+3360w}
\]
and the q=0 branch parameterization
\[
t=39+64h.
\]

The exponent \(E=201+3360w\) is odd and divisible by 3. Reducing the residual identity modulo 3, 5, and 7 gives:

- Modulo 3: \(211\equiv1\), \(1360\equiv1\), \(22155\equiv0\), and \(20\cdot2^E\equiv1\). Hence \(t\equiv0\pmod3\), so \(h\equiv0\pmod3\).
- Modulo 5: \(211\equiv1\), while \(1360,22155,20\equiv0\). Hence \(t\equiv0\pmod5\), so \(h\equiv4\pmod5\).
- Modulo 7: \(211\equiv1\), \(1360\equiv2\), \(22155\equiv0\), and \(20\cdot2^E\equiv6\) because \(E\equiv0\pmod3\). Hence \(t\equiv4\pmod7\), so \(h\equiv0\pmod7\).

Combining these three congruences by CRT:
\[
\boxed{h\equiv84\pmod{105}.}
\]

For the secondary-fan quotient
\[
S=416+684h,
\]
this gives the fixed residue
\[
\boxed{S\equiv17\pmod{105}.}
\]

## Consequence for every deeper bounce depth

The exact source-parent fan has, for each \(r\ge1\), a possible bounce parent
\[
B_{r,h}=(2q-2,\;2487+4096h-q-3r),
\qquad 4^r q=S.
\]

Since \(4^6\equiv1\pmod{105}\), the residue of \(q\pmod{105}\) depends only on \(r\pmod6\). Inverting \(4^r\) gives:

| \(r\bmod6\) | \(4^{-r}\bmod105\) | \(q\bmod105\) |
|---:|---:|---:|
| 0 | 1 | 17 |
| 1 | 79 | 83 |
| 2 | 46 | 47 |
| 3 | 64 | 38 |
| 4 | 16 | 62 |
| 5 | 4 | 68 |

In particular, for every \(r\ge1\),
\[
\boxed{q\ge17,\qquad (B_{r,h})_1=2q-2\ge32.}
\]

There is also an exact residue formula for the second coordinate:
\[
(B_{r,h})_2\equiv 51-q_r-3r\pmod{105},
\]
where \(q_r\) is the table entry for \(r\bmod6\). The pair of coordinates therefore repeats modulo 105 with period dividing 210 in \(r\).

## Research significance and limits

This removes arbitrary \(h\) from the q=0 secondary fan: only \(h\equiv84\pmod{105}\) can arise from the authentic U5 residual root. It also gives a uniform lower bound on the quotient \(q\) in every remaining \(r\ge1\) bounce branch and an explicit odd-modulus residue profile for those parents.

It does **not** prove any \(B_{r,h}\) unreachable. In particular, it does not close the unresolved \(Q+r\pmod4\) branches (odd/even sum 7, or even/even sum zero) identified in the existing secondary-bounce analysis. The next useful step is to combine these fixed mod-105 residues with the exact source-parent grammar for those two residual sectors, rather than enumerate further isolated h-cylinders.
