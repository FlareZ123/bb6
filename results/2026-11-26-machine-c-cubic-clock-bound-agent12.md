# A universal cubic primitive-clock bound for Machine C

Machine C is the historical BB(6) holdout #39, literal table
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. This result is an unconditional bound on the primitive halting time in terms of the terminal rank. It is not an unconditional halting-time bound independent of rank, and does not decide the machine.

## The potential

For the original-source accelerator state $s=(a,k,c)$, set
$$
R(s)=a+2k+c,\qquad G(R)=R^3+6R^2,\qquad F(k)=12k^2+42k,
$$
and $P(s)=G(R(s))+F(k)$. Use the exact transition `nextC` and the primitive cost `weight` from the literal machine's existing source bridge.

**Theorem.** Every successful accelerator edge $s\to t$ satisfies
$$
P(s)+6w(s)\le P(t).
$$
Consequently every weighted finite path of cost $w$ satisfies $P(s)+6w\le P(t)$, regardless of its branch itinerary.

The rank-preserving sweep has $k'=k+1$, and the identity
$F(k+1)-F(k)=6(4k+9)$ pays its entire primitive cost exactly. For rank-increasing resets and bounces, use the identities
$$
G(R+1)-G(R)=3R^2+15R+7,\quad
G(R+3)-G(R)=9R^2+63R+81.
$$
The reset branches reduce the right counter to 0, 1, or 2. Their possible loss of the right-counter potential is bounded by the corresponding rank increment, using $2k\le R$. The other transitions are handled by the same identities and monotonicity. The proof exhausts the actual nine successful rule cases, including the low-counter exceptions. The rank $R$ alone cannot pay rank-preserving sweep costs; $F$ is essential.

For all states, $P(s)\le R^3+9R^2+21R$.

## Literal-machine halting bound

The original raw-machine correspondence states that if the literal machine halts after $N$ successful primitive moves, there is a counted accelerator path from $(5,0,1)$ of weight $w$ ending at a state $t$ with `nextC t = none`, with $N=15+w$. The standard Busy Beaver score is $S=N+1=16+w$.

The initial potential is $P(5,0,1)=432$. Every reachable terminal has $k=2,c=2$ and $a\equiv2\pmod4$: the terminal exception at $(0,0,0)$ is excluded by monotonic rank, and the other possible terminal predecessor is the even bounce. Thus $P(t)=R^3+6R^2+132$. Substitution into the telescoping inequality proves
$$
\boxed{6S+204\le R^3+6R^2.}
$$

In particular, for a proposed champion score $B$, a bound $R\le L$ on all reachable terminal ranks suffices to prove $S\le B$ whenever $L^3+6L^2\le6B+204$. Equivalently, every counterexample to maximality must reach a terminal rank beyond that threshold. It is unnecessary to certify the exact primitive clock of smaller hypothetical terminal candidates.

The theorem does not bound the reachable terminal rank itself. The remaining unbounded reachability question is real, and finite forward scans do not establish its resolution.

## Reproduction

- [RankClock.lean](../im-results/agent12-c-high-shadow/RankClock.lean) contains `edge_budget`, `path_budget`, `potential_rank`, `reachable_terminal_shape`, and `raw_halt_rank_bound`.
- [Original literal bridge](../im-results/agent47-c-root-inverse-audit/CRawCountBridge.lean).
- The initial original-source audit [45755061463](https://github.com/FlareZ123/bb6/actions/runs/45755061463) compiled the generic potential and terminal-edge lemmas but rejected a tactic typo in the root-terminal corollary. Correction [a0c93e88](https://github.com/FlareZ123/bb6/commit/a0c93e88daa7dd5dea7206899cee41cfa353a91b) passed the complete original-source `sourceRankClock` audit [45755243824](https://github.com/FlareZ123/bb6/actions/runs/45755243824). The generic theorem profiles use only standard Lean axioms. The result is proved against the repository's literal six-state machine, not an independent simulator assumption.

## Explicit thin-gateway reduction

The source thin-gateway theorem gives a reachable state (0,2j,4j+10) for every literal halt. Its counted tail ends at (8j+10,2,2), of rank 8j+16. Determinism of terminal weighted paths identifies this with the actual terminal. Hence the score bound is
$$
6S+204\le G(8j+16).
$$
For arbitrary B and J satisfying G(8J+16) <= 6B+204, any literal halt with S>B must reach a thin gateway with j>J. Equivalently, exclusion of every reachable thin gateway with j>J suffices for S<=B. This is the direct statement `raw_bound_of_gateway_tail` consumed at a candidate score; smaller terminal candidates need no exact clock computation. The high/low source criterion already characterizes reachability of these gateways. The tail itself is still unbounded and unresolved.

The gateway bound and both score-transfer corollaries passed the full original-source audit [45755604597](https://github.com/FlareZ123/bb6/actions/runs/45755604597) after correction of an unavailable tactic in the two corollaries.


## Complementary lower clock bound: amortized resets

There is also an original-source theorem giving a nearly matching lower bound. Put $C=\lfloor X/8\rfloor^2$ and $D=8(L+1)$. For any literal halting score $S$, at its actual terminal rank $R$, and arbitrary integers $64\le X\le R<2^L$,
$$
\boxed{CR\le C(X+8+8L)+D(S+2(X+8)^2).}
$$
In particular, with $X=\lfloor R/2\rfloor$ and $L=1+\lfloor\log_2R\rfloor$, the lower-bound function is of order $R^3/\log R$, while the upper-bound function is of order $R^3$. These are explicit bounds conditional on a genuine halt, not a claim that arbitrarily large halting ranks occur in the blank orbit.

**Proof mechanism.** A major reset has $c=0$, or $a=0,c\ge4$. A boundary is a major reset or a terminal state. One boundary jump executes a major transition, drains the resulting rank-preserving sweep in one exact counted path, then performs the $c=1,3$ finishes when necessary. Every such jump raises rank by an integer between 1 and 8.

Write
$$
V(s)=2\max(k+\min(c,3)-3,0)^2,\qquad d(s)=\lfloor\log_2(k+1)\rfloor.
$$
Every successful primitive accelerator transition pays any increase in $V$ with its weight. The major transitions pay in addition a charge $\max(V(s)-8,0)$, because their new stored potential is at most eight and no greater than their literal weight. Classify a major reset as cheap if $4k+9\le R$. The exact jump formula then forces $k'\ge2k+2$, hence $d(t)\ge d(s)+1$. Otherwise, at rank at least $X\ge64$, the major charge is at least $C$. In a band with rank below $2^L$, depth is bounded by $L$. It follows for each jump from $s$ to $t$ of weight $W$ that
$$
CR(t)+8C d(s)+D V(t)\le CR(s)+8C d(t)+D(V(s)+W).
$$
The cheap case uses the depth increase to pay the at-most-eight rank increase. The expensive case spends the charge $DC$ to pay that increase and any depth loss.

A genuine terminal path from the first section $(5,1,0)$ crosses rank $X$ at a boundary with rank below $X+8$. Its stored potential there is at most $2(X+8)^2$. Telescoping the jump inequality to the terminal, discarding nonnegative terms, bounding final depth by $L$, and using the original literal clock correspondence proves the displayed lower bound. This covers low-counter exceptions and both stopping families without any assumed section-frequency distribution.

**Source proof:** [ResetClockLower.lean](../im-results/agent12-c-high-shadow/ResetClockLower.lean), including `cheap_growth`, `major_charge`, `terminal_band_budget`, `terminal_clock_lower`, and `raw_terminal_clock_bounds`. The complete original-source audit [45757025919](https://github.com/FlareZ123/bb6/actions/runs/45757025919) passed at [7ab4607a](https://github.com/FlareZ123/bb6/commit/7ab4607ac9ac4b10046387cff2db1228bba24362) after supplying the explicit first section transition in the raw bridge. It combines both score inequalities at one genuine reachable terminal, with only standard Lean axioms. A reachable thin gateway of sufficiently large index must therefore yield a score above any fixed proposed bound; between the sufficient upper and lower rank thresholds, the inequalities alone do not decide the score.
