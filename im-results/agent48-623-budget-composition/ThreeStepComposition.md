# Root-mass composition for a three-transition terminal chain

**Status:** proof plan with checked arithmetic; not yet a Lean theorem. The n=10 mass-corridor wrappers and the fixed-depth terminal helper are separate intermediate files. This note records how their hypotheses could compose.

## 1. Target chain and state indexing

Let q be a genuine blank-root state at scale n, with successful source transitions
[
q\longrightarrow p\longrightarrow h\longrightarrow\mathrm{halt}.
]
The root-mass exclusion is applied to q. The terminal ratio-four theorem is applied to p, because p is the terminal parent of the final two transitions. The source root-ray bridge is applied to q→p. This is the correct indexing for a three-transition chain; no two-step safety theorem is being used to infer three-step survival.

Assume
[
m=\min(q_1,q_2),\qquad 3^{n-1}-3\le m\le3^n-4,\qquad n\ge10.
]

## 2. Uniform q→p output bound

The four source bridge sectors give the following upper bounds for p's second coordinate (the drain depth is n):
| q sector | source upper bound for p₂ |
|---|---:|
| odd far-left | (3m+16+4n) |
| even far-left | (3m+10+4n) |
| odd near-left | (3m+4n+2) |
| even near-left | (3m+6n+9) |

The even-near bound dominates for n≥10. Since (m\le3^n-4),
[
p_2\le3m+6n+9\le3^{n+1}+6n-3. \tag{1}
]

These are the source leaves that must be obtained from `drainB_upper_linear_log` and, in the even-near sector, `evalA_upper_log` followed by `drainB_upper_linear_log`.

## 3. Apply the terminal-parent corridor at p

Because p→h→halt, the source theorem
`blank_root_two_step_terminal_parent_corridor`
applies to p. Its angular corridor gives, in either parity case,
[
p_1+p_2\le17p_2+68.
]
Combining with (1),
[
p_1+p_2\le M_n:=51\cdot3^n+102n+17. \tag{2}
]

The terminal ratio-four source theorems can be instantiated uniformly with
[
N=n+2,\qquad K=n+5.
]

- Far-left drain block conditions follow from
  (p_2+3\le3^{n+1}+6n<3^{n+2}).
- Odd near-left has (p_1\le p_2+4), hence (p_1-1<3^{n+2}).
- Even near-left has (p_1\le p_2), hence (p_1<3^{n+2}).
- The largest hK premise is the odd far-left one. By (2),
[
2(p_1+2p_2+10+3N)+5
\le4M_n+6n+37
=204\cdot3^n+414n+105
<243\cdot3^n=3^{n+5}
]
for n≥10. The final inequality follows by elementary induction from n=10.

Thus the four `TerminalRatio4Source` branches yield a terminal ratio-four window on p of width at most
[
B_n=K+8N+17=9n+38. \tag{3}
]
The other three branch widths are (6n+44), (6n+35), and (6n+27), all smaller for n≥10.

## 4. p's exceptional even gap-two branch

The p corridor also supplies `∀k, ¬gateBudget p₁ p₂ k`. If p were in the exceptional even branch (p_1=p_2+2), use (k=n+6).

From (1) and the even corridor,
[
p_1<16p_2+44
<48\cdot3^n+96n-4
<3^{n+6}.
]
On the other hand, strict source mass growth gives
[
p_1+p_2\ge q_1+q_2+7
\ge2m+7
\ge2\cdot3^{n-1}+1.
]
If (p_1=p_2+2), this forces (p_1\ge3^{n-1}+2), so
[
2(n+6)+6\le3p_1
]
for n≥10. These are exactly the remaining premises of the even gap-two disjunct of `gateBudget p₁ p₂ (n+6)`, contradicting the p corridor's no-gate conclusion.

Consequently p lies in one of the four source terminal sectors and (3) applies.

## 5. Combined cancellation budget

The q→p root-ray bridge error is at most
[
e_n=26n+46,
]
and the additive offset is at most 9. Combining with (3),
[
B_n+e_n+9
=(9n+38)+(26n+46)+9
=35n+93
\le E_n:=35n+120. \tag{4}
]
There is a uniform 27-unit margin in the root mass-corridor allowance.

The four existing bridge wrappers are designed to consume exactly this shape of terminal window on p and source bridge on q. For near q sectors, the scale band is initially on (m=\min(q_1,q_2)). The combined bridge and terminal window force (q_1\le q_2): if (q_1>q_2\), the far-terminal/near-q bridge would imply
(|q_2-13q_1|\le E_n), although (13q_1-q_2\ge12q_2\ge12m>E_n); the near-terminal/near-q bridge would imply
(|7q_1-4q_2|\le E_n), although (7q_1-4q_2\ge3q_2\ge3m>E_n).
Thus the n-scale band transfers to q₁, as required by the near wrappers.

If the corresponding q root-mass corridor excludes all four cancellation strips, (4) contradicts q's genuine root membership.

## 6. Separate q even gap-two branch

The q branch (q=(m+2,m)) is not one of the four ray sectors. Its mass interval is
[
2\cdot3^{n-1}-4\le q_1+q_2\le2\cdot3^n-6.
]
It therefore needs a separate root-mass bracket. Candidate exact brackets from the current BigInt source-shaped replay are:

| n | q gap-two mass interval | lower checkpoint | upper checkpoint | candidate root indices |
|---:|---:|---|---|---|
| 10 | [39362, 118092] | run 32: 38429 | run 37: 127572 | 33–36 |
| 11 | [118094, 354288] | run 36: 98859 | run 42: 510164 | 37–41 |
| 12 | [354290, 1062876] | run 41: 347700 | run 47: 1423655 | 42–46 |

The n=10 version is already present as `n10_even_gap_two_root_excluded` in `RootMassGapAllN10.lean`. Draft n=11/n=12 checkpoint declarations and all six corresponding finite exclusions now live in `RootMassGapN11N12.lean`; they remain uncompiled.

## 7. Concrete remaining proof obligations

1. Source-prove the four q→p third-coordinate bounds and extract the branch-specific `drainB`/`evalA` equalities from `highLevelNext`.
2. Compile `TerminalWindowAtDepth12.lean` as the n=10 instance; generalize it to (N=n+2,K=n+5) if extending to n=11,12.
3. Compose the q bridge inequalities with the p terminal window and call the matching root-mass wrapper.
4. Compile `RootMassGapN11N12.lean`: its run 47–55 `by decide` checkpoints and n=11/n=12 near, far, and q-gap-two exclusions are drafted but not yet source-checked.
5. Keep all of this in `im-results/` until the complete source composition and checkpoint dependencies compile without `sorryAx`.

No #623 nonhalting conclusion, and no exact BB(6) value, follows until these obligations are completed. The root mass corridors are finite-scale evidence, not an all-time invariant.


### Exact run 47–55 checkpoint candidates

The source-shaped BigInt replay gives the following additional exact states; each should become a Lean `by decide` checkpoint before it is used in a root-mass proof:

| step | state D(a,d) | mass |
|---:|---|---:|
| 47 | D(145494,1278161) | 1423655 |
| 48 | D(1132670,436504) | 1569174 |
| 49 | D(696164,1309542) | 2005706 |
| 50 | D(613374,2088523) | 2701897 |
| 51 | D(1475146,1840152) | 3315298 |
| 52 | D(365000,4425473) | 4790473 |
| 53 | D(4060470,1095032) | 5155502 |
| 54 | D(2965430,3285134) | 6250564 |
| 55 | D(319702,8896323) | 9216025 |

These agree with the existing source-checked checkpoints through run 46 in `RootMassGapAllN10.lean`; run 47–55 themselves remain unverified until `decide` is compiled against the original imports.
