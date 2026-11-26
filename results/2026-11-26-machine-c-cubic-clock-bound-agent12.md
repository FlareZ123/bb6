# A universal cubic primitive-clock bound for Machine C

Machine C is the historical BB(6) holdout #39, literal table
`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. This result is an unconditional bound on the primitive halting time in terms of the terminal rank. It is not an unconditional halting-time bound independent of rank, and does not decide the machine.

## The potential

For the original-source accelerator state (s=(a,k,c)), set
[
R(s)=a+2k+c,\qquad G(R)=R^3+6R^2,\qquad F(k)=12k^2+42k,
]
and (P(s)=G(R(s))+F(k)). Use the exact transition `nextC` and the primitive cost `weight` from the literal machine's existing source bridge.

**Theorem.** Every successful accelerator edge (s\to t) satisfies
[
P(s)+6w(s)\le P(t).
]
Consequently every weighted finite path of cost (w) satisfies (P(s)+6w\le P(t)), regardless of its branch itinerary.

The rank-preserving sweep has (k'=k+1), and the identity
(F(k+1)-F(k)=6(4k+9)) pays its entire primitive cost exactly. For rank-increasing resets and bounces, use the identities
[
G(R+1)-G(R)=3R^2+15R+7,\quad
G(R+3)-G(R)=9R^2+63R+81.
]
The reset branches reduce the right counter to 0, 1, or 2. Their possible loss of the right-counter potential is bounded by the corresponding rank increment, using (2k\le R). The other transitions are handled by the same identities and monotonicity. The proof exhausts the actual nine successful rule cases, including the low-counter exceptions. The rank (R) alone cannot pay rank-preserving sweep costs; (F) is essential.

For all states, (P(s)\le R^3+9R^2+21R).

## Literal-machine halting bound

The original raw-machine correspondence states that if the literal machine halts after (N) successful primitive moves, there is a counted accelerator path from ((5,0,1)) of weight (w) ending at a state (t) with `nextC t = none`, with (N=15+w). The standard Busy Beaver score is (S=N+1=16+w).

The initial potential is (P(5,0,1)=432). Every reachable terminal has (k=2,c=2) and (a\equiv2\pmod4): the terminal exception at ((0,0,0)) is excluded by monotonic rank, and the other possible terminal predecessor is the even bounce. Thus (P(t)=R^3+6R^2+132). Substitution into the telescoping inequality proves
[
\boxed{6S+204\le R^3+6R^2.}
]

In particular, for a proposed champion score (B), a bound (R\le L) on all reachable terminal ranks suffices to prove (S\le B) whenever (L^3+6L^2\le6B+204). Equivalently, every counterexample to maximality must reach a terminal rank beyond that threshold. It is unnecessary to certify the exact primitive clock of smaller hypothetical terminal candidates.

The theorem does not bound the reachable terminal rank itself. The remaining unbounded reachability question is real, and finite forward scans do not establish its resolution.

## Reproduction

- [RankClock.lean](../im-results/agent12-c-high-shadow/RankClock.lean) contains `edge_budget`, `path_budget`, `potential_rank`, `reachable_terminal_shape`, and `raw_halt_rank_bound`.
- [Original literal bridge](../im-results/agent47-c-root-inverse-audit/CRawCountBridge.lean).
- The initial original-source audit [45755061463](https://github.com/FlareZ123/bb6/actions/runs/45755061463) compiled the generic potential and terminal-edge lemmas but rejected a tactic typo in the root-terminal corollary. Correction [a0c93e88](https://github.com/FlareZ123/bb6/commit/a0c93e88daa7dd5dea7206899cee41cfa353a91b) passed the complete original-source `sourceRankClock` audit [45755243824](https://github.com/FlareZ123/bb6/actions/runs/45755243824). The generic theorem profiles use only standard Lean axioms. The result is proved against the repository's literal six-state machine, not an independent simulator assumption.
