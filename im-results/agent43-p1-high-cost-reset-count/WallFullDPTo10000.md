# Finite all-depth shifted-wall exclusion through n=10000

**Agent 43 — 2026-11-13.** This is an exact, reproducible finite computation built on Agent 50's source-wall telescoping identity and modular subset recurrence. It is not yet Lean-kernel checked. All conclusions below are conditional on the source-wall identity being applied to the authentic P1 inverse history.

## Result

For every critical index \(14\le n\le10000\), the exact shifted wall

\(b+4m+4n+20=12\cdot2^n\)

has no source-path endpoint, with no restriction on inverse depth, provided the source telescoping identity holds.

The proof is a two-stage finite carry computation:

1. The modular subset scan leaves exactly six possible indices:
   (30,8), (286,88), (350,112), (1614,563), (2990,1068), (3342,1145).
2. For each of those six indices, a second exact BigInt carry DP for the full wall equation reaches the empty state set after finitely many terminal costs. No exact target carry occurs before that point.

The self-contained executable is [WallFullDPTo10000.js](WallFullDPTo10000.js). It reruns the complete n=14..10000 modular scan, then all six full-wall scans, and asserts the exact candidate list and all empty-state certificates.

## Source identity being used

Write \(P=2^n\). For a source path with inverse costs \(e_i=t_i+1\), cumulative costs

\(0=s_0<s_1<\cdots<s_{k-1}<s_k=m\),

put

\(S=\sum_{i<k}2^{s_i}\), \(T=\sum_{i<k}s_i2^{s_i}\).

The exact wall telescoping identity from [Agent 50's derivation](../agent50-p1-dyadic-width/wall_cost_telescoping.md) is

\[
P(7S-2^m)=2^m(m+n+3)+(n+3)S+T-1. \tag{W}
\]

In particular, folding the terminal term into the sum gives

\[
\sum_{i=0}^{k}(n+3+s_i)2^{s_i}\equiv1\pmod{2^n}. \tag{M}
\]

The first DP uses only this necessary modular condition. The second DP uses the full equality (W).

### Derivation from the unchanged-source inverse relation

The source state is the original counted inverse state \((b,d,m,z)\) of Agent 28's [OneResetCount.lean](../agent28-p1-word-automaton/OneResetCount.lean). The unchanged-source inverse characterization is [inverseAt_iff_power_mass](../agent1-p1-quarter/InverseIff.lean). For fixed \(n\), put \(P=2^n\).

The source mass identity

\[
b+d+2m+2n+13=14P
\]

holds at the root and is preserved by every CountCone parent step. Indeed, if an inverse step of depth \(t\) returns \((k,c)\), its output is
\((b',d',m')=(2k-4,c+4,m+t+1)\). The second inverseAt equation, using the source guard \(c\bmod2=1\), gives
\(2k+c+2t+2=b+d\), which makes the mass expression unchanged.

The first inverseAt equation is
\[
d+b/2+3=2^t(c+3).
\]
Combining it with the mass identity yields
\[
2^{t+1}(c+3)=d+14P-2(m+n+6)+5.
\]
With \(e=t+1\), \(s=m\), \(x=d-1\), and \(x'=d'-1=c+3\), this is exactly
\[
x=2^e x'-14P+2s+2n+6.
\]

For a path with successive costs \(e_j\) and cumulative starts
\(s_0=0,\ s_{j+1}=s_j+e_j\), multiply the recurrence at step \(j\) by \(2^{s_j}\) and sum. The \(x_j\)-terms telescope, giving
\[
2=2^m x_k-14PS+2(n+3)S+2T,
\]
because the root has \(d_0=3\), hence \(x_0=2\). At the shifted wall,
\(b+4m+4n+20=12P\), the mass identity gives
\(d_k=2P+2m+2n+7\), hence \(x_k=2P+2m+2n+6\). Substitution and division by two gives (W). Thus (W) follows from the actual unchanged-source CountCone transitions and the shifted-wall endpoint equation; it is not a simulator extrapolation.

### Why the carry recurrences are exhaustive

At bit \(j\), suppose the carry after the lower \(j\) bits is \(c\), and choose the next subset bit \(x_j\in\{0,1\}\). If the required target bit is \(\epsilon_j\), the next carry exists exactly when
\(c+x_jC_j\equiv\epsilon_j\pmod2\), and is then
\((c+x_jC_j-\epsilon_j)/2\). Induction on the processed bit count shows that the DP state set is exactly the set of carries arising from all allowed subset choices. The forced initial bit \(x_0=1\) enforces \(0\in A\).

For the modular phase, \(\epsilon_0=1\) and \(\epsilon_j=0\) for \(j>0\). The extra gap-state coordinate records the distance to the previous selected bit, capped at 2; the short-gap counter increments exactly for gaps 1 or 2. Merging equal (carry, gap-state) pairs while retaining the minimum counter cannot remove a future transition, since all future transitions depend only on those two coordinates. For the full-wall phase, every target bit is 1 because the right side is a multiple of \(2^m\) minus 1. The terminal carry is therefore exactly \(P+m+n+3\). Empty state sets stay empty under every later transition.

## Phase 1: exhaustive modular scan, n=14..10000

Let \(x_s=1\) iff \(s\) belongs to the truncated cumulative-cost set \(A_n\subseteq\{0,\ldots,n-1\}\). It contains \(0\), and (M) implies

\[
\sum_{s=0}^{n-1}x_s(n+3+s)2^s\equiv1\pmod{2^n}.
\]

For even \(n\), the forced bit \(x_0=1\) leaves initial carry \(c=(n+2)/2\); odd \(n\) is impossible. At each bit \(j\ge1\), with \(C_j=n+3+j\), the exact transitions are:

- omit \(j\) if \(c\) is even: \(c'=c/2\), and the gap state advances;
- select \(j\) if \(c+C_j\) is even: \(c'=(c+C_j)/2\), and the short-gap count increases exactly when the previous selected position is at distance 1 or 2.

The DP stores the minimum short-gap count for each exact pair (carry, capped gap state). Thus a terminal state exists iff a subset satisfying the modular congruence exists. The scan finds exactly:

| n | minimum adjacent gaps of 1 or 2 |
|---:|---:|
| 30 | 8 |
| 286 | 88 |
| 350 | 112 |
| 1614 | 563 |
| 2990 | 1068 |
| 3342 | 1145 |

All other \(n\in[14,10000]\) have empty terminal state sets and are excluded by (M).

The first phase uses JavaScript Number, but all values are exact: \(0\le c\le2n+2\le20002\), \(C_j\le2n+2\), and all gap/count variables are at most \(n\). The script asserts the carry and coefficient safe-integer bounds on every transition.

## Phase 2: full wall equation for the six survivors

For a fixed candidate \(n\), let \(P=2^n\) and \(Q=7P-(n+3)\). The full equation (W) is equivalent to

\[
\sum_{s\in A}(Q-s)2^s=2^m(P+m+n+3)-1,
\]

where \(A\subseteq\{0,\ldots,m-1\}\) contains \(0\). After processing \(m\) bits of the left-hand sum, the carry \(c_m\) must therefore equal

\[
c_m=P+m+n+3.
\]

The second DP starts with state set \(\{0\}\), forces \(x_0=1\), and at each bit \(j\) considers both \(x_j=0\) and \(x_j=1\). For \(C=Q-j\), it retains the next carry \((c+x_jC-1)/2\) exactly when the numerator is odd. This enumerates every subset with the required low bits; the full equation requires the exact target carry above.

All second-phase arithmetic uses BigInt. The results are:

| n | last nonempty m | first empty m | peak carry states | exact target hits |
|---:|---:|---:|---:|---:|
| 30 | 81 | 82 | 44 | 0 |
| 286 | 1441 | 1442 | 504 | 0 |
| 350 | 585 | 586 | 152 | 0 |
| 1614 | 5823 | 5824 | 1544 | 0 |
| 2990 | 6153 | 6154 | 3040 | 0 |
| 3342 | 13729 | 13730 | 7488 | 0 |

Once the state set is empty it remains empty under every later transition. Therefore no larger \(m\) can solve the full wall equation for any of the six candidate indices.

## Interpretation and limits

Combining the two phases excludes the shifted wall for all \(14\le n\le10000\), including arbitrary high-depth source excursions. This is stronger than the earlier finite \(14\le n\le147\) carry check and stronger than a five-shallow restriction on this finite interval.

The result is computational, not a Lean-kernel-certified theorem. The source identity is currently recorded as a derivation in Agent 50's note; a source-connected Lean proof and a formal certificate for both DPs remain to be written. It does not cover \(n>10000\), prove P1 nonhalting, settle exceptional inverse exits, or determine BB(6). Keep this artifact in im-results, not results.

## Carry-target correction (2026-11-13)

An independent audit of the full-wall carry found that the original script and the first version of this note used P+m+n+2. The correct target is P+m+n+3. Indeed, from (W), with Q=7P−(n+3),

    ∑_{s∈A}(Q−s)2^s = 2^m(P+m+n+3)−1.

The full-wall bit DP processes the target residue −1, so after m bits its carry is (sum+1)/2^m and must equal P+m+n+3. WallFullDPTo10000.js was corrected accordingly in commit ef0ec2e4c8abff90a05421e4a554f2d0de566902.

The corrected exact BigInt rerun for all six modular candidates still has no exact target hits and the same empty-state indices. Thus the finite n≤10000 exclusion is unchanged; the previous +2 only made the exact-hit diagnostic incorrect. The empty-state argument already excluded every larger m after the first empty layer.

The source identity is now independently kernel-checked in [WallTelescopingSource.lean](WallTelescopingSource.lean): theorem source_wall_cost_identity derives the natural weighted-sum identity from the authentic original CountCone history, exact inverseAt characterization, source mass invariant, and shifted-wall endpoint. Its axiom audit has no sorryAx. The theorem currently returns existential aggregates S,U rather than an explicit Finset of edge starts; PR #99 drafts that stronger interface but is not yet verified. Accordingly, the carry scan is still computational evidence conditional on the source-to-finite-subset bridge, not a fully kernel-checked all-depth wall exclusion.

The corrected independent output summary is preserved in [WallFullDPTo10000-output.json](WallFullDPTo10000-output.json), including all six modular candidates, their exact empty-state indices, peak state counts, and the n=30 mod-2^15 audit.
