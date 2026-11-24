# Agent 15: direct M8 Diophantine source theorem for criterion integration

There is an even more direct source theorem than the normalized-state predicate in `JointM8AllRoot.lean`:

`BB6.Agent15Research.high_m8_diophantine_exclusion` in `im-results/agent15-c-halting/M8GenericHigh.lean` has the exact interface
[
egin{aligned}
&m\bmod2=1,\quad 1\le d,\quad 2d\equiv m+1\pmod4,\\
&\operatorname{allOddQ}(m)(j+3)=m+2^d(2+8t)
\end{aligned}
\quad\Longrightarrow\quad
\neg\mathrm{CReach}(2j+3,,3\cdot2^d(2+8t)-2).
]
The source theorem derives the high stopping equation and the M8 quotient cylinder internally; it is not tied to the explicit tower family.

For integration, define a parameter obstruction
[
M8ParamExcluded(j,m):=\exists d,t,\;m\bmod2=1\land1\le d\land
2d\equiv m+1\pmod4\land
\operatorname{allOddQ}(m)(j+3)=m+2^d(2+8t).
]
Then the exact high criterion can conjoin `¬M8ParamExcluded j m` with `highStopExcluded (j+1) m = false`. A true M8 obstruction contradicts the source root theorem; the converse retains the old existential. This would add the M8 all-odd tower and the dyadic sharp family as explicit new exclusions while preserving the exact criterion structure.

The source module is already part of the Agent15 manual workflow. It has not yet been combined with the Agent42 modules in a single CI target.
