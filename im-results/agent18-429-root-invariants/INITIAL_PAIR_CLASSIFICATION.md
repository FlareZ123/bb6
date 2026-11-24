# Exact first-pair classification for the branch-29 signed inverse tree

This note sharpens the even-F-run reduction in [SIGNED_F_RUN_PARITY.md](SIGNED_F_RUN_PARITY.md). It is an exact theorem about the compressed signed inverse system, not yet a Lean theorem and not by itself a source-root certificate.

## Initial state and F-run formula

Write \(t=k+1\), where \(c=3k+4\) is the branch-29 parameter. Immediately after the forced initial F-block, the compressed signed state is
\[
u=48t,\qquad D=96t+18=2u+18.
\]
A run of \(m\) further F-blocks ends at \((u_m,D_m)\), where
\[
u=2^m u_m,\qquad
D_m=D+6(u-u_m)+3m=8u-6u_m+18+3m.
\]
The next paired block can only be:
- EF, when \(u_m\) is odd and \(D_m\equiv0\pmod8\);
- SF, when \(u_m\) is even and \(D_m\equiv4\pmod8\).

Since \(8u\equiv0\pmod8\) and \(18\equiv2\pmod8\),
\[
D_m\equiv -6u_m+2+3m\pmod8.
\]

## Refined endpoint table

Solving this congruence together with the parity of \(u_m\) gives exactly:

| Next block | \(m\bmod8\) | \(u_m\bmod4\) |
|---|---:|---:|
| EF | 0 | 3 |
| EF | 4 | 1 |
| SF | 2 | 2 |
| SF | 6 | 0 |

No other pair of residues can end an F-run at a paired block.

## The exact parameter classification

**The first paired transition exists if and only if**
\[
\boxed{k\equiv2\pmod4\quad\text{or}\quad k\equiv15\pmod{16}.}
\]

*Necessity.*

For EF, \(u_m\) is odd, so \(m\) is the full 2-adic valuation of \(u=2^4\cdot3t\). If \(m\equiv0\pmod8\), then \(m\ne0\) because \(u\) is even, hence \(m\ge8\). Thus \(2^8\mid u\), so \(2^4\mid t\), giving \(k\equiv15\pmod{16}\).

If \(m\equiv4\pmod8\), either \(m=4\) or \(m\ge12\). In the latter case \(2^{m-4}\mid3t\) with \(m-4\ge8\), again giving \(16\mid t\). In the former case \(u_m=3t\), and the table requires \(3t\equiv1\pmod4\), hence \(t\equiv3\pmod4\), or \(k\equiv2\pmod4\).

For SF, if \(m\equiv2\pmod8\), the case \(m=2\) is impossible: \(u_m=12t\equiv0\pmod4\), whereas the table requires \(u_m\equiv2\pmod4\). Therefore \(m\ge10\), so \(2^{m-4}\mid3t\) with \(m-4\ge6\), and in particular \(16\mid t\).

If \(m\equiv6\pmod8\), the table gives \(4\mid u_m\). Therefore \(2^{m+2}\mid u\). Since \(m\ge6\), \(2^8\mid u=2^4\cdot3t\), so \(16\mid t\). Thus every SF endpoint requires \(k\equiv15\pmod{16}\).

*Sufficiency.*

If \(k\equiv2\pmod4\), then \(t\equiv3\pmod4\). Choose \(m=4\). We have \(u_m=3t\), which is odd and \(1\pmod4\); the table (or the displayed congruence) gives \(D_m\equiv0\pmod8\). Hence EF is available.

If \(k\equiv15\pmod{16}\), then \(16\mid t\). Choose \(m=6\). We have \(u_m=3t/4\), which is divisible by \(4\); the displayed congruence gives \(D_m\equiv4\pmod8\). Hence SF is available.

This proves the equivalence.

## Exact first block and consequence

The first paired transition is uniquely located at the first eligible F-run endpoint:
- If \(k\equiv2\pmod4\), it is EF after exactly 4 further F-blocks.
- If \(k\equiv15\pmod{16}\), it is SF after exactly 6 further F-blocks.
- For every other \(k\), no paired transition is possible at any point on the F-spine. The inverse path is only the F-spine and terminates when \(u_m\) becomes odd.

Consequently, **11/16 of all integer parameters \(k\ge0\)** are eliminated at the initial signed-inverse stage. Only the two residue families above can reach a paired block. The \(k\equiv15\pmod{16}\) family is the 2-adic neighborhood of the exceptional \(k=-1\) (equivalently \(c=1\)) pure-F spine; the \(k\equiv2\pmod4\) family is a separate surviving branch.

The remaining task is now sharply focused: analyze the post-EF branch for \(k\equiv2\pmod4\) and the post-SF branch for \(k\equiv15\pmod{16}\), and determine whether subsequent paired transitions refine these classes toward a 2-adic exceptional parameter. This note does not claim that either surviving family contains an infinite path.
