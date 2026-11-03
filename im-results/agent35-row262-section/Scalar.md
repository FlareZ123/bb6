# A one-dimensional dyadic return map for BB(6) historical row 262

**Agent 35, 2026-11-03. Intermediate original mathematical derivation.** The underlying exact six-state state-A section equations are Lean checked at [Row262.lean](Row262.lean) and [Row262Complete.lean](Row262Complete.lean), with independent raw transition parsing and tests in [test_row262.py](test_row262.py). The *full scalar encoding and its iff with blank halting* are proved mathematically by the calculation below, **but have not themselves been Lean formalized**. No externally checked priority/novelty judgment or resolution of the root is claimed.

Machine, rooted at blank A: `1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---`. The absent F/1 action halts. The machine is retained in the historical October30 608-row roster; the current research-status ledger requires separate provenance verification.

## 1. A single nonnegative dyadic rational encodes each state-A tape

With the physical head at integer coordinate `p`, let `t_i∈{0,1}` be the tape bit at absolute coordinate `i` (finitely many 1s). At a state-A checkpoint define

`x = ∑_{i∈Z} t_i 2^(p-i) ∈ Z[1/2]_{≥0}.`

Equivalently, the bits at the head and successive positions to its left form the ordinary integer part `N=floor(x)` (head bit is the least significant bit), while the bits at `p+1,p+2,...` form the finite binary fractional part `f=x-N∈[0,1)`. Consequently `N%2=t_p` and the `j`th digit of `f` is exactly `t_(p+j)`. The finite binary expansion is unique because the tape has finite 1-support. Thus `x` completely specifies the physical tape **relative to the head**, with state A understood. The absolute coordinate `p` is discarded, which is legitimate for deciding blank-tape halting because a global tape translation preserves all transitions.

## 2. Exact partial scalar map and primitive runtime

Let `e=v₂(N+1)` when `N` is odd, so `e≥1`. Let `b₃=floor(8f)%2` and `b₄=floor(16f)%2`. The following partition is exhaustive:

| Condition on `N,f` | Next state-A scalar `F(x)` | Primitive steps | Head shift |
| --- | --- | ---: | ---: |
| `N` odd | `(x+1)/2^(e+1)` | `e+3` | `-e-1` |
| `N` even, `0≤f<1/2` | `x+3/2` | 2 | 0 |
| `N` even, `3/4≤f<1` | **HALT**, undefined `F(x)` | 2 | +2 |
| `N` even, `1/2≤f<3/4`, `b₄=0` | `32(x+1)` | 5 | +5 |
| `N` even, `1/2≤f<3/4`, `b₄=1, b₃=0` | `4x+17/4` | 6 | +2 |
| `N` even, `1/2≤f<3/4`, `b₄=1, b₃=1` | `2x+17/8` | 7 | +1 |

The head shift in the halting row is the position of frozen F/1 relative to the previous state-A head; no next A state exists. Each nonhalting output is again a nonnegative dyadic rational.

### Derivation

The [exhaustive original-action A-section table](README.md#complete-primitive-step-state-a-branches) proves exactly which cells change and by how much the head moves for every finite tape. Define the absolute-coordinate potential `V(T)=sum_{i:t_i=1}2^(-i)`, so `x=2^p V(T)`. If a macro changes `V` by `c*2^(-p)` and moves the head by `d`, then

`x'=2^(p+d)(V+c*2^(-p))=2^d(x+c).`

The branch coefficients `c` are respectively `1,3/2,1,1,17/16,17/16` for the six table rows. For the odd row, the initial head 1 and `k` consecutive left ones are exactly the `k+1` trailing 1-bits of integer `N`; the first left 0 ensures `e=v₂(N+1)=k+1`, and the physical head shift is `d=-k-2=-e-1`. This gives `F=(x+1)/2^(e+1)`, duration `k+4=e+3`. For even `N`, the binary fractional digits select the other five rows directly. The values `b₃,b₄` select precisely the recorded cell guards. The formula for each output is then just the displayed identity `x'=2^d(x+c)`. This establishes the scalar return map for every state-A configuration with finite tape support.

### Exact blank-origin halting criterion

Define `x₀=0`. While an iterate lies outside the halting region

`H={x∈Z[1/2]_{≥0} : floor(x) is even and 3/4≤x-floor(x)<1},`

set `x_(n+1)=F(x_n)` with the table above. The original blank-A Turing machine **halts if and only if a finite scalar iterate x_n enters H**.

Proof: the encoding gives the exact original blank A tape at `x₀=0`. For any A checkpoint outside `H`, the universal Lean-certified A-section theorems show that the machine returns to A in a finite, positive number of primitive steps with precisely the next tape and head displacement in the table. The table's only halting row has `t_p=0,t_(p+1)=t_(p+2)=1`, exactly `H`, and reaches frozen F/1 in two primitive steps. A frozen halt is absorbing, so a section known to end at A cannot have halted earlier. Induction on the sequence of A checkpoints transfers the entire original raw run into scalar iterates until and unless it halts. All rows of the exhaustive table have been accounted for. As long as the orbit avoids `H`, each scalar step gives a finite genuine primitive run, yielding arbitrarily long nonhalting prefixes. Conversely any finite raw halting time lies in one of these A sections, hence in the halting row. The scalar map is an exact translation-invariant recoding of the source six-state machine's halting question, without claiming that this halting question is decidable.

If the first halting scalar index is `n`, the precise raw primitive step score is

`2 + ∑_(j=0)^(n-1) duration(x_j)`.

Both the physical head offset and full head-relative tape can also be reconstructed from the table, so the scalar model loses no halting/runtime information.

## 3. Reproducible discrimination and limits

The independent Python 3 standard-library [test_scalar.py](test_scalar.py) implements only the rational formulas above, compares with a separately written raw-table section transformer, checks 10,000 seeded arbitrary synthetic finite A tapes, then checks every complete A checkpoint of the original blank run within the separate 200,000-primitive-step budget. It uses exact `fractions.Fraction`, no floating-point approximation.

First scalar iterates from the actual blank start:

`0 → 3/2 → 5/8 → 52 → 107/2 → 109/8 → 117/32 → 149/256 → ...`

The independently implemented raw and rational paths agree on **42,388 complete A sections** ending at primitive time **199,996**. This is a finite reproduction, and the global iff comes from the preceding symbolic case proof rather than finite experiment.

The scalar formula collapses the two-sided finite physical tape and state-A transition logic to a **piecewise affine one-dimensional map of dyadic rationals** with an odd-sector `v₂(N+1)` division and one explicit halting interval. No simple invariant excluding `H` from the special orbit `F^n(0)` has been established. The exact value of BB(6) is unknown. The result belongs in `im-results/` pending independent original-source formalization, literature review, transfer to other roots, and a genuinely blank-rooted decision.

## 4. High-priority follow-up

Seek a global arithmetic or symbolic-language invariant of the single dyadic orbit `0,F(0),F²(0),...` that excludes `H`, or find a verified finite iterate in `H`. In particular, investigate the normalized numerator, denominator exponent, and binary digit language after the odd `v₂(N+1)` branch. Many simple congruence or finite-prefix invariants are insufficient because the map is expanding on even branches and has unbounded odd valuation. Avoid deriving nonhalting from the observed finite 42,388 safe sections.
