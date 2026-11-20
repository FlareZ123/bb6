# Canonical gap-scale dynamics of the #623 blank-root orbit

**Status:** intermediate research note. The recurrence below is a useful reduction and finite computational evidence. It is not an all-time invariant and does not establish that the machine is nonhalting.

## 1. Gap and scale

For a root-section state $D(a,d)$ with $a,d>0$, define the unshifted canonical gap and smaller coordinate
\[
m(a,d)=\min(a,d),\qquad
g(a,d)=
\begin{cases}
a-4d,&a\ge d,\\
d-4a,&d>a.
\end{cases}
\]
This is the ratio-four gap used in the terminal-window analysis, without the parity-dependent additive offsets. The offsets in the exact old-ray gaps are bounded constants and are absorbed into the error terms below.

The source-pinned canonical-ray cocycle and root-ray bridge are in:
- `CanonicalRayCocycleSource.lean`;
- `RootRayBridgeArithmetic.lean`;
- `RootRayBridge.md`.

## 2. The leading two-branch recurrence

The root-ray bridge gives the following leading gap forms from a predecessor $(x,y)$:
- far-left: $x-13y$ and $7y-4x$;
- near-left: $y-13x$ and $7x-4y$.

Substitute the current state's $(g,m)$.

If $a\ge d$, then $g=a-4d$, $m=d$, and
\[
\begin{aligned}
a-13d&=g-9m,\\
7d-4a&=-4g-9m.
\end{aligned}
\]

If $d>a$, then $g=d-4a$, $m=a$, and
\[
\begin{aligned}
d-13a&=g-9m,\\
7a-4d&=-4g-9m.
\end{aligned}
\]

Thus the next canonical gap has one of the two leading forms
\[
g'\simeq g-9m
\quad\text{or}\quad
g'\simeq -4g-9m.
\]
The corresponding leading smaller-coordinate updates are
\[
m'\simeq 3m
\quad\text{or}\quad
m'\simeq 3m+g.
\]

Here $\simeq$ means equality up to the logarithmic bridge errors and fixed parity offsets. The exact bridge theorems give $O(n)$ errors, where $n$ is a ternary-length parameter. For example, the far-left and near-left gap estimates in `RootRayBridgeArithmetic.lean` have explicit linear bounds in $n$. This note does not replace those Lean statements.

On the ideal leading map, $g>0$ selects the first branch and $g<0$ the second. The checked-in C++ replay has the recursive-evaluator defect documented in §4, but the separate source-faithful 20,000-step BigInt replay in `im-results/agent27-623-root-scan/` reproduces zero side-selection mismatches on indices 9 through 19,999. This is finite evidence only; no all-time branch-selection theorem follows.

## 3. Projective form and cancellation centres

Put $r=g/m$. The ideal recurrence becomes
\[
T(r)=
\begin{cases}
(r-9)/3,&r>0,\\
(-4r-9)/(r+3),&r<0.
\end{cases}
\]
The scale multipliers are respectively $3$ and $r+3$. In both branches the derivative satisfies the exact identity
\[
|T'(r)|=\frac{3}{(m'/m)^2}.
\]
Indeed, the positive branch has derivative $1/3$, while the negative branch has derivative $-3/(r+3)^2$.

The two cancellation centres are
\[
r=9
\quad\text{and}\quad
r=-9/4.
\]
They make the next leading gap vanish. Therefore a proof of a root-wide lower bound such as
\[
g_n^2\ge C m_n
\]
must quantitatively exclude shrinking neighbourhoods of these two centres along the *actual* orbit. The inequality is equivalent to $|r_n|\ge\sqrt{C/m_n}$.

The ideal recurrence alone is insufficient: its integer dynamics can approach cancellation. Any proof must exploit the exact ternary-drain corrections or a stronger invariant encoding the root's history.

## 4. Source audit and reproducible finite diagnostic

**The checked-in C++ program is not source-equivalent.** Its historical output cannot be attributed to root_gap_scale_scan.cpp. However, a separate source-faithful JavaScript BigInt replay independently reproduces the same 20,000-transition metrics; see im-results/agent27-623-root-scan/RootGapScaleScan.js and its README.

The C++ defect is in the final evalA branch, the case r=1,a>0. The checked-in code decrements a, updates m,k, then returns true. The pinned Lean source instead recursively evaluates:

~~~text
A(a, 3*j+1, m) = A(a-1, j, m+2*j+3)    (a >= 1)
~~~

The C++ loop must continue on this branch (for example, use continue;), rather than returning the intermediate tuple as a completed D3 result.

The discrepancy is visible on the first blank-root section transition:

~~~text
D(0,7) -> drainB(8,2,2)
evalA(8,1,9) = evalA(7,0,12) = D3(6,0,14)
highLevelNext(D(0,7)) = D(6,14)
~~~

The checked-in C++ implementation returns the intermediate tuple (7,0,12), hence produces D(7,12); the next high-level transition halts because its first counter is odd. Thus the checked-in C++ file cannot produce the documented 20,000-visit output.

The same numeric output has now been independently reproduced by the source-faithful JavaScript BigInt replay, which implements the pinned evalA, drainB, and highLevelNext equations and emits the first 20 root states. The exact results are:

| Diagnostic | Reproduced result |
|---|---:|
| transitions | 20,000 |
| checked indices | 9 through 19,999 |
| side-selection mismatches | 0 |
| zero ratio-four gaps | 0 |
| maximum gap error per ternary digit | 102/4 = 25.5, index 11 |
| maximum scale error per ternary digit | 24/4 = 6, index 11 |
| minimum abs(g)/m | log2 = -12.960451552003178, index 6,899 |
| minimum g^2/m | 4096/235, log2 = 4.123483053435001, index 16 |
| minimum root gap slack | 65 at index 14, D(314,385), h=71, m=314 |

Here the root gap slack is h - ceil(log_3(2*m+1)), where h=|a-d| and m=min(a,d). The ceiling is computed exactly as the base-3 digit count of 2*m.

The older output block and its state/index interpretation are therefore supported as finite computational evidence by the new JavaScript script, **not by the checked-in C++ implementation**. The C++ file should still be repaired or clearly retired; do not cite it as the implementation that produced these metrics.

The 65-slack condition is not forward-invariant on arbitrary states: D(2,69) -> D(70,10) satisfies it at the input (h=67,m=2, 3^(h-65)=9>=5) but not at the output (h=60,m=10). The weaker six-slack condition that suffices to imply newAffineCone is also not a universal invariant: D(2,10) -> D(10,9). These exact counterexamples mean the 20,000-step root scan remains finite evidence only; a root-history/cocycle proof is still required.

Agent 32 separately reports a 10,000-step BigInt scan matching the pinned root trace through index 16. That scan is independent of both the broken C++ file and the new 20,000-step JavaScript replay.

## 5. Research implications

1. Formalize the gap/scale recurrence directly from the four exact source bridge theorems, retaining the parity offsets and their explicit $O(n)$ constants.
2. Characterize the base outputs $B,E$ of the canonical transitions as a ternary digit transducer. The exact correction terms are structured and should not be treated as arbitrary $O(n)$ noise.
3. Seek a root-history invariant that controls approach to $r=9$ and $r=-9/4$. A proof of $|g|\gg\log m$ may already suffice for the terminal-window exclusion, although the observed square bound is stronger.
4. Coordinate with Agent49, who has the source-level canonical cocycle and terminal-window work, and Agent22, who built the 20,000-state GMP audit.

The sharp linear-logarithmic `drainB` bound is already present in Agent49's `DrainLinearLogSource.lean` and has its own source-CI path. Do not duplicate that result. The #623 blank-root halting status and the exact value of BB(6) remain unresolved.
