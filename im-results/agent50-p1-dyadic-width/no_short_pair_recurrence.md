# Exact pair-carry recurrence for the six-shallow subset condition

**Status:** exact reduction; the resulting logarithmic no-short-run bound is a conjectural target, not proved here.

This note develops the modular condition
\[
\sum_{s\in A}(n+3+s)2^s\equiv1\pmod{2^n},\qquad 0\in A\subseteq\{0,\ldots,n-1\},
\]
without repeating the finite-width scan. It reduces the proposed six-shallow lower bound to a precise bound on runs of pair transitions that create no gap of length 1 or 2.

## 1. Bit-carry recurrence

Let
\[
c_1=(n+2)/2,\qquad
c_{j+1}=\frac{c_j+x_j(n+3+j)}2,
\]
where \(x_j\in\{0,1\}\) indicates whether \(j\in A\). Each quotient must be integral. The bit-zero choice is forced to be \(x_0=1\), and the displayed modular congruence is equivalent to the existence of this integral carry path through bits \(1,\ldots,n-1\).

For even \(n\), a path is impossible unless \(n\equiv2\pmod4\): at odd bit \(j=1\), the coefficient \(n+4\) is even, so the incoming carry \(c_1\) must be even. Assume henceforth \(n\equiv2\pmod4\).

At odd bit \(j=2k+1\), the coefficient is
\[
n+3+j=n+4+2k=2H_k,\qquad H_k=n/2+k+2.
\]
The carry at an odd bit must be even, so write \(c_{2k+1}=2a_k\). Choose \(x\in\{0,1\}\) at the odd bit and put \(u=a_k+xH_k\). At the following even bit the coefficient is \(2H_k+1\), which is odd; its bit choice \(y\) is therefore forced by parity:
\[
y\equiv u\pmod2.
\]
For the carry at the next odd bit to be even, one further needs
\[
4\mid u+y(2H_k+1).
\]
The next pair state is exactly
\[
a_{k+1}=\frac{a_k+xH_k+y(2H_k+1)}4.
\]
The initial pair state is \(a_0=(n+2)/4\). There are \((n-2)/2\) complete pairs (bits \(1,2\) through \(n-3,n-2\)); the final bit \(n-1\) can be omitted, so it cannot improve a minimum-gap counter.

## 2. Exact no-short transition system

Let \(g_k\in\{0,1,2\}\) be the capped distance-minus-one from the current odd bit \(2k+1\) to the last selected bit:
\[
g_k=\min(2,(2k+1)-s_{\rm last}-1).
\]
Initially \(g_0=0\), because bit zero is selected. A gap is *short* if its length is 1 or 2.

The four pair choices and their exact arithmetic requirements are:

| pair bits \((x,y)\) | integrality requirement | next carry | gap update |
|---|---|---|---|
| 00 | \(4\mid a\) | \(a/4\) | \(\min(2,g+2)\) |
| 10 | \(4\mid a+H\) | \((a+H)/4\) | \(1\) |
| 01 | \(4\mid a+2H+1\) | \((a+2H+1)/4\) | \(0\) |
| 11 | \(4\mid a+3H+1\) | \((a+3H+1)/4\) | \(0\) |

The pair 11 always creates an adjacent selected pair, hence a short gap. The other transitions are no-short exactly under these additional gap-state conditions:

- **00:** always no-short;
- **10:** no-short iff \(g=2\);
- **01:** no-short iff \(g\ge1\);
- **11:** never no-short.

Thus every no-short run is a path in the following exact three-transition system, with \(H\) incremented by one each pair:
\[
\begin{array}{rcll}
(a,g)&\xrightarrow{00}&(a/4,\min(2,g+2))&
  4\mid a,\\
(a,2)&\xrightarrow{10}&((a+H)/4,1)&
  4\mid a+H,\\
(a,g\ge1)&\xrightarrow{01}&((a+2H+1)/4,0)&
  4\mid a+2H+1.
\end{array}
\]
All divisions here are exact integer divisions. This is a convenient Lean formalization target: the parity choice at the even bit has already been eliminated.

## 3. Consequence for the six-shallow lemma

A path with at most five short gaps has at most five pair positions at which a short gap is created. Removing those pair positions partitions the \((n-2)/2\) pairs into at most six consecutive no-short runs. Consequently, a uniform bound
\[
L(n)\le C\log_2(n+2)
\]
on the length of every no-short run, from any reachable gap state, would imply
\[
(n-2)/2\le 6L(n)+5.
\]
For sufficiently large \(n\) this is impossible. The remaining finite range could be handled by the existing exact carry DP (rather than by an unbounded scan).

**The missing theorem is precisely the logarithmic no-short-run bound.** The recurrence above does not by itself prove it: the 01 and 10 transitions inject terms of size comparable to \(n\), so a naive contraction estimate \(a'\le(a+2n+O(1))/4\) has a positive fixed point.

## 4. Exact arithmetic for a fixed no-short word

Encode no-short transition types by \(t_k\in\{0,1,2\}\), corresponding to 00, 10, 01. Their carry updates have the form
\[
a_{k+1}=\frac{a_k+\alpha_k n/2+\beta_k}{4},
\]
where
\[
(\alpha_k,\beta_k)=
\begin{cases}
(0,0)&t_k=0,\\
(1,k+2)&t_k=1,\\
(2,2k+5)&t_k=2.
\end{cases}
\]
For a fixed word of length \(r\), iterating gives the exact integrality condition
\[
A_r n+B_r\equiv0\pmod{4^{r+1}},
\]
with
\[
A_r=1+\sum_{k<r}2\alpha_k4^k\quad(\text{odd}),\qquad
B_r=2+\sum_{k<r}\beta_k4^{k+1}.
\]
Thus each fixed no-short word determines one residue class of \(n\pmod{4^{r+1}}\). The gap-state restrictions constrain the admissible words. This is a useful alternative to enumerating all subsets, but a counting argument over words alone is not enough to prove a per-\(n\) bound.

## 5. Reproducible exploratory data

The exact no-short transition DP gives these maximal initial no-short run lengths (in *pairs*, not bits):

| \(n\) | maximal no-short pairs |
|---:|---:|
| 4,094 | 11 |
| 34,990 | 18 |
| 761,406 | 19 |
| 2,731,582 | 22 |

For even \(n\in[14,10{,}000]\), an exhaustive run of the no-short state recurrence found a maximum of 11 pairs (at \(n=4{,}094\)). The longer examples show that a constant bound is false; logarithmic growth is a plausible target. These data are exploratory, not proof.

The no-short path for \(n=34{,}990\) survives 18 pairs and then dies. Near its end, the unique surviving branch has carry states
\[
556\to139\to4411\to9856\to2464\to616\to154\to4416\to1104\to276\to69,
\]
with the transition labels \(00,00,10,01,00,00,00,10,00,00,00\) over the corresponding final pairs. This illustrates why a naive monotone-carry argument fails: 10/01 can re-inject a carry of order \(n\).

## 6. Return-cycle decomposition of no-short runs

After the first pair, the gap state is \(g=2\) whenever a no-short run is at a return point. Write \(0=00\), \(1=10\), and \(2=01\). Every first-return segment from \(g=2\) back to \(g=2\) has exactly one of these forms:
\[
0^r\ (r\ge1),\qquad
0^r10,\qquad
0^r20,\qquad
0^r120\quad(r\ge0).
\]
This follows directly from the gap graph: after 10 the next no-short transition is either 00 or 01; after 01 the next transition must be 00; and 00 returns to gap state 2.

If the segment starts at carry \(a\) and parameter \(H\), its ending parameter is \(H+\ell\), where \(\ell\) is its length, and the exact ending carry is:
\[
\begin{array}{c|c|c}
\text{segment}&\ell&a_{\rm end}\\
\hline
0^r&r&a/4^r\\
0^r10&r+2&(a+4^r(H+r))/4^{r+2}\\
0^r20&r+2&(a+4^r(2H+2r+1))/4^{r+2}\\
0^r120&r+3&(a+4^r(9H+9r+12))/4^{r+3}.
\end{array}
\]
All displayed quotients are exact. In particular, any segment with an initial \(0^r\) requires \(4^r\mid a\), so its initial zero-run has length at most \(\lfloor\log_4 a\rfloor\). This bounds the zero-run *inside one return segment*, but it does not bound the number of return segments. The remaining logarithmic-run problem is therefore to bound the number of admissible return segments, using the coupled divisibility conditions in these four affine maps.

## 7. Suggested next step

Prove or refute the following focused statement:

> There is an absolute constant \(C\) such that every consecutive no-short run in the pair recurrence has length at most \(C\log_2(n+2)\).

A useful proof will likely need to exploit the *joint* base-4 divisibility conditions across 10/01 transitions, not just the size bound on \(a_k\). A counterexample family would be equally valuable: it would identify whether the six-shallow subset lemma needs a different route.
