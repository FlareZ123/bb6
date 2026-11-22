# Agent 24: residual-one branch closes to a 36-step +5 growth macro

Important update to my previous residual-one handoff: I have now explicitly derived the output of the concrete (L=[0]) token bounce, so the tempting (+5) recurrence is no longer just a hypothesis.

For
[
T(s)=\texttt{tok\_DR}([2,0],[(s,0)],[0]),
]
the pinned source lemmas give:
[
\begin{aligned}
T(s)
&\xrightarrow{4}\texttt{tok\_DR}([2,1,0],[(s,0)],[])\\
&\xrightarrow{8}\texttt{tok\_EL}([1,0],[(s,0)],[0,1])\\
&\xrightarrow{2}\texttt{tok\_EL}([0],[(s,0)],[0,0,1])\\
&\xrightarrow{1}\mathrm{CR}([(0,0),(0,0),(1,0)],[(s+1,0)]).
end{aligned}
]
The exact CR/EL/DL/DR mode branches then take 21 steps back to (T(s+5)). Thus
[
\boxed{T(s)\to^{36}T(s+5)\quad(s\ge0).}
]
Iterating proves an infinite, nonhalting forward orbit from every (T(s)).

The residual-one root branch from the previous note reaches
[
T(s),quad
s=391054452683042459868759864,
]
after its finite CR/EL/DL/DR prefix. So **conditional on the preceding E(13) root chain**, this is a source-level nonhalting continuation.

Full step-by-step macro and caveats:
`im-results/agent24-cryptid-root-proof/ResidualOneGrowthMacro.md`.
The parameter chain into the residual-one endpoint:
`im-results/agent24-cryptid-root-proof/Residual1BranchContinuation.md`.

This is not yet a compiled Lean theorem, and it does not prove blank-root reachability of (E_{160771976531}(13)). The next highest-value action is to write/compile the 36-step macro as a kernel-checked `ReachesPlus` theorem, then integrate the upstream root prefix under the Critic's compile-first gate. Do not dispatch CI as a substitute for local preflight.
