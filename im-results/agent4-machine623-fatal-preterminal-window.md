# Sharper preterminal gap window from the exact fatal-spectrum pullback

**Status:** exact conditional arithmetic composition of existing source-derived statements. The depth bounds used below are present in the current research notes but the combined wrapper has not yet passed pinned-source CI. This is an intermediate result, not an all-time decision of the authentic blank-root orbit.

## Setup and hypotheses

Let a genuine canonical-ray input state be (D(a,d)), with
[
q=\min(a,d),\qquad p=|a-d|,\qquad g=p-3q.
]
Let its successful one-step output be (D(a',d')), and suppose the output is terminal:
[
\operatorname{highLevelNext}(D(a',d'))=\texttt{none}.
]
Write (p'=|a'-d'|). Let (n\ge10) be the source depth parameter and assume the joint-mass envelope
[
a'+d'\le 6\cdot3^n+12n+28.
]
The source fatal-spectrum pullback in `FatalSpectrumPullbackSource.lean` then gives:
- odd output third counter: (p'\le n+6) on left output, (p'\le n-3) on right output;
- even output third counter: (p'\le n+3) on left output, (p'\le n) on right output.

The canonical-ray cocycle has exact output difference
[
a'-d'=g-T,\qquad p'=|g-T|,
]
with
[
T=3D+2r+c_s,
\quad c_{LO}=19,\ c_{LE}=10,\ c_{RO}=-4,\ c_{RE}=4.
]
Here (D) is the signed drain first-counter drop and (r) the outer drain count. Assume the current drain-depth estimates
[
|D|\le \ell+1,\qquad 0\le r\le\ell,\qquad \ell\le n+1.
]
The last two estimates are the ones that still need to be packaged with the exact source consumer.

## Sector-specific interval calculation

The depth assumptions imply the following exact enclosing intervals:
[
egin{array}{c|c}
s&T\ \hline
LO &[16-3\ell,\ 5\ell+22]\\
LE &[7-3\ell,\ 5\ell+13]\\
RO &[-3\ell-7,\ 5\ell-1]\\
RE &[1-3\ell,\ 5\ell+7].
\end{array}
]
The output parity is odd for LO and RE, and even for LE and RO. Since left output means (g=T+p') and right output means (g=T-p'), combining the branch-specific (p')-bounds with the intervals above gives:

| Input sector | Left-output interval for (g) | Right-output interval for (g) | Combined interval after (ell\le n+1) |
|---|---:|---:|---:|
| LO | ([17-3\ell,\ 5\ell+n+28]) | ([19-3\ell-n,\ 5\ell+21]) | ([16-4n,\ 6n+33]) |
| LE | ([9-3\ell,\ 5\ell+n+16]) | ([7-3\ell-n,\ 5\ell+13]) | ([4-4n,\ 6n+21]) |
| RO | ([-3\ell-5,\ 5\ell+n+2]) | ([-3\ell-n-7,\ 5\ell-1]) | ([-4n-10,\ 6n+7]) |
| RE | ([2-3\ell,\ 5\ell+n+13]) | ([4-3\ell-n,\ 5\ell+6]) | ([1-4n,\ 6n+18]) |

Thus the preterminal input gap is bounded by
[
\boxed{
\begin{array}{c|c}
LO&|g|\le6n+33\\
LE&|g|\le6n+21\\
RO&|g|\le6n+7\\
RE&|g|\le6n+18.
\end{array}}
]
In particular, a uniform bound is (|g|\le6n+33), improving the earlier common (9n+23) envelope for every (n\ge10).

## Old-ray distance bounds

Using the exact canonical distance conversions
[
h=g-9\ (LO),\quad h=g-5\ (LE),\quad
h=(g-1)/2\ (RO),\quad h=(g-2)/2\ (RE),
]
and the sector parity of (g), the same intervals yield
[
\boxed{
\begin{array}{c|c}
LO&|h|\le6n+24\\
LE&|h|\le6n+16\\
RO&|h|\le3n+3\\
RE&|h|\le3n+8.
\end{array}}
]
These improve the prior source-supported terminal-window envelopes (6n+44), (6n+31), ((6n+19)/2), and ((9n+25)/2), respectively.

## Derivation and evidence boundary

The only nontrivial inputs are:
1. `odd_terminal_gap_bound` and `even_terminal_gap_bound` in `im-results/agent1-machine623-3euclidean-correction-bounds/FatalSpectrumPullbackSource.lean`;
2. the exact (p'=|g-T|) output map and (T)-constants in `im-results/agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md`;
3. (|D|\le\ell+1), (r\le\ell), and (ell\le n+1) from the drain-depth analysis.

The interval arithmetic is elementary once those hypotheses are supplied. The fatal-spectrum source module and the combined depth wrapper must still be compiled together against the pinned original machine before this is called a source-certified theorem. It does **not** prove that the authentic (D(0,7)) orbit avoids these windows, and it does not decide #623 or BB(6).

**Potential use:** feed these narrower, sector-specific preterminal windows into the existing root-history / 3-adic carry and cancellation arguments. The remaining decisive task is still all-time exclusion on the authentic root, not another finite scan.
