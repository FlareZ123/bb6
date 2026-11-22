# Residual-one 36-step growth macro

**Status:** source-exact finite macro derived from the pinned #85 module's token and stack transition lemmas. The macro is not yet compiled as a standalone Lean theorem in this repository. It proves an infinite forward orbit from the stated token family; reaching that family from the blank root remains conditional on the preceding root path.

## The token family

For (s\in\mathbb N), write
[
T(s)=\texttt{tok\_DR}([2,0],[(s,0)],[0]).
]
The pinned source module has the exact lemmas:
[
egin{aligned}
\texttt{tok\_DR\_zero}&:\quad
\texttt{tok\_DR}([2,0],R,[0])
\to^{4}
\texttt{tok\_DR}([2,1,0],R,[]),\\
\texttt{tok\_DR\_nil\_8}&:\quad
\texttt{tok\_DR}([2,1,0],R,[])
\to^{8}
\texttt{tok\_EL}([1,0],R,[0,1]),\\
\texttt{tok\_EL\_1}&:\quad
\texttt{tok\_EL}([1,0],R,[0,1])
\to^{2}
\texttt{tok\_EL}([0],R,[0,0,1]),\\
\texttt{tok\_EL\_exit\_zero}&:\quad
\texttt{tok\_EL}([0],R,[0,0,1])
\to^{1}
\mathrm{cfg\_CR\_n\_n}([(0,0),(0,0),(1,0)],\operatorname{bumpPairHead}(R)).
end{aligned}
]
For (R=[(s,0)]), (operatorname{bumpPairHead}(R)=[(s+1,0)]). Therefore the token prefix is exactly 15 raw machine steps:
[
T(s)\to^{15}
\mathrm{CR}([(0,0),(0,0),(1,0)],[(s+1,0)]).
]

## The 21-step stack return

Starting from that CR state, the pinned source's mode lemmas give the following exact path:

| Raw steps | Source mode | Configuration after the macro |
|---:|---|---|
| 2 | CR, first left zero | (mathrm{CR}([(0,0),(1,0)],[(s+3,0)])) |
| 2 | CR, second left zero | (mathrm{CR}([(1,0)],[(s+5,0)])) |
| 6 | CR, left head one and empty tail | (mathrm{EL}([(0,0)],[(0,0),(s+8,0)])) |
| 2 | EL, right head zero | (mathrm{EL}([(0,0),(0,0)],[(s+8,0)])) |
| 1 | EL, positive right head | (mathrm{DL\_0\_n}([(0,0),(0,0)],[(s+7,0)])) |
| 4 | DL, positive right head at least two | (mathrm{DR}([(0,0),(0,0)],[(1,0),(s+5,0)])) |
| 4 | DR, left head zero/right head one | (T(s+5)) |

The last 4-step branch is the direct `texecute 4` path in `mode_DR_n_n_closed` before its generic `tok_DR_2_0_closed` continuation. We stop at the resulting token configuration; we do not assume the output of the generic closure theorem.

The stack portion costs (2+2+6+2+1+4+4=21) raw steps. Combined with the 15-step token prefix:
[
\boxed{T(s)\to^{36}T(s+5)\quad\text{for every }s\ge0.}
]

Every branch condition is uniform in (s\ge0): the positive EL head is (s+8\ge8), and the positive DL head is (s+7\ge7). Thus the same macro applies at every iterate.

## Infinite-orbit consequence

Iterating the exact macro gives
[
T(s)\to^{36}T(s+5)\to^{72}T(s+10)\to^{108}\cdots.
]
The parameter is unbounded and each macro has positive length. Hence **no configuration (T(s)) halts**. This is a source-level nonhalting theorem for the entire token family (T(s)), conditional only on the correctness of the cited pinned-source transition lemmas. It does not depend on the generic `tok_DR_2_0_closed` theorem's existential output.

## Connection to the residual-one root branch

The preceding file `Residual1BranchContinuation.md` reaches
[
\mathrm{CR}(0^{r+9}1,[0]),qquad
r=195527226341521229934379923.
]
Applying the exact source CR/EL/DL/DR mode transitions:
- the (r+9) leading left zeros take (2(r+9)) steps and increment the right head to (2(r+9));
- the CR-one branch takes 6 steps and produces EL with right stack ([0,2r+21]);
- the EL-zero, EL-positive, DL-positive, and DR-one/zero branches take (2+1+4+4=11) further steps.

The resulting token state is
[
T(s),\qquad s=2r+18=391054452683042459868759864.
]
Thus this residual-one endpoint reaches a proven infinite-growth family after (2r+35) additional raw steps. The subsequent machine run is nonhalting.

## What this does and does not establish

This closes the local residual-one continuation: once the conditional root path reaches the stated residual-one endpoint, the machine cannot halt. It does **not** yet establish that the blank-tape root reaches (E_{160771976531}(13)), the (E(13)) chain, or this residual-one endpoint. Those upstream source macros and the blank-root prefix still require a single compiled Lean reachability theorem. Do not report this as a complete blank-root nonhalting proof or as a BB(6) result until that reachability gate is met.


## Source-local Lean append draft

`ResidualOneGrowthMacro.append.lean` now contains source-local theorem drafts, intended to be concatenated after `RootCountdownSweep.append.lean` and `RootRemainderTwoToken.append.lean` inside the pinned source module:

- `agent24_tok_DR_growth_step`: direct `texecute 36) proof of (T(s)\to^+T(s+5)).
- `agent24_tok_DR_growth_iter`: induction by `ReachesPlus.trans), giving arbitrarily long forward paths.
- `agent24_s_residual_one_to_cr`: source-lemma proof that (S(1,k+1)) exits to the CR stack with (k+10) zeros.
- `agent24_cr_residual_one_to_growth`: composes the parameterized CR/EL/DL/DR macros and the direct four-step DR-to-token entry to reach (T(2r+18)).
- `agent24_s_residual_one_to_growth`: composes the previous two lemmas.

Each theorem has a `#print axioms` command in the append. These are **drafts only**: the local Lean preflight has not run, and the Critic's acceptance gate prohibits CI dispatch until it succeeds locally. The append must be concatenated inside the source module because `tok_DR`, `tok_EL`, and encoding helpers are private.


The append also gives a generic composition, not just the concrete root instance. For every (k\ge0), it proves
[
\texttt{tok\_DR}([2,1,1,1,1,1,0],[],0^{k+1}1)
\to^+
\mathrm{CR}(0^{k+10}1,[0])
\to^+
T(2k+20).
]
Equivalently, every residual-one (S(1,r)) state with (r\ge1) reaches (T(2r+18)), and hence has an infinite forward orbit. The concrete root branch has (r=195527226341521229934379923), giving (T(391054452683042459868759864)).
