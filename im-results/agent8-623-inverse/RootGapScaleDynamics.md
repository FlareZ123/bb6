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

On the ideal leading map, $g>0$ selects the first branch and $g<0$ the second. A finite root replay below found no side-selection mismatch after the canonical-ray entry point. This branch-selection observation is computational evidence, not an all-time theorem.

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

## 4. Reproducible finite diagnostic

`root_gap_scale_scan.cpp` is a source-shaped GMP mirror of the accelerated `evalA`, `drainB`, and `highLevelNext` definitions. It starts at $D(0,7)$, accepts a step count, and tracks:
- whether $g>0$ agrees with the next state's $a'\ge d'$;
- the error in the two leading gap/scale updates, normalized by the ternary digit length of $m$;
- the minimum $|g|/m$;
- the minimum $g^2/m$.

Build and run:
\`\`\`sh
g++ -O3 -std=c++17 root_gap_scale_scan.cpp -lgmpxx -lgmp -o root_gap_scale_scan
./root_gap_scale_scan 20000
\`\`\`

Completed 20,000-step run:
\`\`\`text
DONE steps=20000 mismatch=0 zero=0
max |eg|/ternaryDigits log2=4.67243 index=11 error_bits=7 m_bits=6
max |em|/ternaryDigits log2=2.58496 index=11 error_bits=5 m_bits=6
min |g|/m log2=-12.9605 index=6899
min g^2/m log2=4.12348 index=16
\`\`\`

The maximum gap error is exactly $102$ at the transition from $D(312,38)$ to $D(268,138)$: the leading prediction is $-182$, while the actual unshifted gap is $-284$. The scale error there is $24$. These are finite maxima, not universal constants.

The minimum square ratio is $4096/235$, attained at index 16, state $D(876,235)$, where $g=-64$ and $m=235$. The normalized gap becomes much smaller elsewhere: at index 6899 the diagnostic records $\log_2(|g|/m)\approx-12.9605$. Consequently a uniform cone estimate $|g|\ge c m$ is contradicted by this finite trace, even though the square-gap margin remains positive throughout the scan.

This program is an independent source-shaped mirror, not a Lean proof or a substitute for the original-source CI chain. The existing 20,000-state audit in `im-results/agent22-623-root-ray-20k/` is complementary evidence. Attempts to extend this particular local diagnostic to 30,000 and 100,000 steps exceeded the available command timeout; no conclusion is drawn from those attempts.

## 5. Research implications

1. Formalize the gap/scale recurrence directly from the four exact source bridge theorems, retaining the parity offsets and their explicit $O(n)$ constants.
2. Characterize the base outputs $B,E$ of the canonical transitions as a ternary digit transducer. The exact correction terms are structured and should not be treated as arbitrary $O(n)$ noise.
3. Seek a root-history invariant that controls approach to $r=9$ and $r=-9/4$. A proof of $|g|\gg\log m$ may already suffice for the terminal-window exclusion, although the observed square bound is stronger.
4. Coordinate with Agent49, who has the source-level canonical cocycle and terminal-window work, and Agent22, who built the 20,000-state GMP audit.

The sharp linear-logarithmic `drainB` bound is already present in Agent49's `DrainLinearLogSource.lean` and has its own source-CI path. Do not duplicate that result. The #623 blank-root halting status and the exact value of BB(6) remain unresolved.
