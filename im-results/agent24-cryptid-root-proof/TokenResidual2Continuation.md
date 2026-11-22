# Agent 24: exact token-normalizer continuation through the first residual-2 branch

**Status:** source-lemma derivation and exact integer arithmetic; not yet Lean-compiled. This continues the unresolved token input at the end of `RootRemainderOneTail.md`.

## Parameterized token state

Define
[
S(x,r)=\operatorname{tok\_DR}([2,x,1,1,1,1,0],[],0^r++[1]).
]

The pinned source lemmas yield three useful transitions.

### Subtract-three cycle

For (x\ge3),
[
S(x,r)\longrightarrow^+S(x-3,r+4)
]
with raw cost (6r+35):
- (r) applications of `tok_DR_zero`;
- `tok_DR_1_nil_28`;
- (r+1) applications of `tok_EL_1`;
- `tok_EL_add3`.

For (N) successive cycles starting at (S(x,3)), the total cost is
[
\sum_{j=0}^{N-1}(6(3+4j)+35)=12N^2+41N.
]

### Zero-remainder branch

At (x=0),
[
S(0,r)\longrightarrow^+S(2r+7,3)
]
with raw cost (8r+77).

After the (r) `tok_DR_zero` steps, `tok_DR_1_nil_28`, and (r+1) `tok_EL_1` steps, the state is
[
\operatorname{tok\_EL}([0,1,1,1,1,0],[],0^{r+4}1).
]
Then:
- `tok_EL_0_cons` gives `tok_CR([2,1,1,1,0],[],0^(r+4)1)`;
- (r+4) `tok_CR_zero` steps give `tok_CR([2r+10,1,1,1,0],[],[1]));
- `tok_CR_1_nil_33` and `tok_EL_add3` give (S(2r+7,3)).

The raw cost is
[
4r+28+2(r+1)+1+2(r+4)+33+5=8r+77.
]

### Residual-2 branch

At (x=2),
[
S(2,r)\longrightarrow^+
CR(0^5++[1]++0^{r+3}++[1],[0])
]
with raw cost (6r+46).

After the same initial (r)-zero reduction and `tok_DR_1_nil_28), (r+1) `tok_EL_1) steps leave
[
\operatorname{tok\_EL}([2,1,1,1,1,0],[],0^{r+4}1).
]
Apply `tok_EL_2), four `tok_EL_1) steps, and `tok_EL_exit_zero). The left list becomes (0^5 1 0^{r+3}1); the empty right suffix bumps to ([0]).

For completeness, the analogous (x=1) branch gives (CR(0^{r+9}1,[0])) at cost (6r+41).

## Specialization to the unresolved root token input

The final section of `RootRemainderOneTail.md` gives, with (n=8{,}841{,}438),
[
\operatorname{tok\_DR}([2,0],[],0^3 1 0^{4n+6}1).
]

The initial source-lemma sequence is:
- three `tok_DR_zero` steps;
- `tok_DR_succ`;
- (4n+7) `tok_CR_zero` steps;
- `tok_CR_1_nil_33`;
- `tok_EL_add3`.

It reaches (S(8n+12,3)) at raw cost (8n+67). The preceding DL-right-one entry contributes 4 more raw steps.

Exact parameters:

| Stage | (x) | subtract-three cycles (N) | resulting (r) |
|---|---:|---:|---:|
| Initial | 70731516 | — | 3 |
| First zero branch | 0 | 23577172 | 94308691 |
| Second zero branch | 188617389 | 62872463 | 251489855 |
| Residual-2 branch | 2 | 167659905 | 670639623 |

The arithmetic is:
[
x_1=2(3+4N_0)+7=188{,}617{,}389,
]
[
x_2=2(3+4N_1)+7=502{,}979{,}717\equiv2\pmod3.
]
Thus the third batch takes ((x_2-2)/3) cycles and enters the residual-2 branch.

| Component | Raw steps |
|---|---:|
| Initial token prefix to (S(x_0,3)) | 70731571 |
| First subtract-three batch | 6670597440875060 |
| First zero branch | 754469605 |
| Second subtract-three batch | 47435361822007411 |
| Second zero branch | 2011918917 |
| Third subtract-three batch | 337318131809364405 |
| Residual-2 branch | 4023837784 |
| **From token input to residual-2 CR state** | **391424097933204753** |
| Including the preceding DL-right-one entry | **391424097933204757** |

The resulting stack state is
[
CR(0^5++[1]++0^{670639626}++[1],[0]).
]
Its CR left head is 0, so this endpoint is not in the source's CR halting branch.

## Immediate ordinary-stack continuation

The source clauses give a further exact prefix:
[
egin{aligned}
CR(0^5 1 0^{r+3}1,[0])
&\longrightarrow^+CR(1 0^{r+3}1,[10])\\
&\longrightarrow^+CR(0^{r+3}1,[0,13])\\
&\longrightarrow^+CR([1],[2r+6,13])\\
&\longrightarrow^+EL([0],[0,2r+9,13]).
end{aligned}
]
For (r=670639623), the final right stack is ([0,1341279255,13]).

## Conditional cumulative raw-step arithmetic

The preceding `RootRemainderOneTail.md` gives a conditional cumulative total of (153{,}499{,}683{,}790{,}849) raw steps through (D_0(26{,}524{,}315;[0,0,2])). The suffix-preserving countdown from there to (D_{8{,}841{,}438}(1;[0,0,2])) costs
[
12N^2+57N=938052814856094.
]
Combining that conditional prefix with the present source-lemma derivation gives
[
\boxed{392515650431851700}
]
raw steps from blank to the displayed residual-2 CR state.

This is **not a certified runtime lower bound**: the prior root path, suffix-preserving maps, and this token composition still require kernel-checked Lean proofs. It is a reproducible source-lemma target for the next formalization step.
