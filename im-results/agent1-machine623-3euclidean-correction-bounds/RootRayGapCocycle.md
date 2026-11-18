# Exact old-ray gap cocycle in two drain statistics

**Status:** algebraic consolidation of the existing canonical-ray, exact-drain, and weighted-correction lemmas. It is an exact recurrence for canonical-ray transitions, not a blank-root nonhalting proof. Keep in im-results/.

## Coordinates and drain statistics

Write the current state in one of the four canonical affine rays, with affine shift \(t\ge0\). Let
\[
g=p-3q,\qquad m=q,\qquad p=|a-d|,\quad q=\min(a,d).
\]
The branch-specific old-ray distance \(h\) is
\[
h=
\begin{cases}
g-9 & \text{left-odd (LO)},\\
g-5 & \text{left-even (LE)},\\
(g-1)/2 & \text{right-odd (RO)},\\
(g-2)/2 & \text{right-even (RE)}.
\end{cases}
\]

Use two integer statistics of the canonical drain:
- \(D\): the signed first-counter drop relative to the canonical base, so the final base first counter is its baseline minus \(D\);
- \(r\): the number of outer drain iterations.

For LO, LE, and RO, \(D=L-2e\) in the valuation normal form, where \(L\) is the valuation-run length and \(e\) counts the terminal-digit-2 cases. For RE, \(D\) includes the signed drop from the initial evalA call as well as the subsequent drain drop. In every sector, \(r\) is the outer drain iteration count appearing in the exact weighted correction identity.

The correction variables from ExactRayCorrectionRelations.lean are
\[
\beta=B-c-v,\qquad \delta=E-3m,
\]
where \(B,E\) are the canonical base output counters and \(c,v\) are the sector's fixed baseline parameters. Combining the exact first-counter formula with the weighted identity gives:

| Input sector | Canonical current state | \(\beta\) | \(\delta\) | \(\delta+2\beta\) |
|---|---|---:|---:|---:|
| LO | \(d\) odd, \(a=d+5+k+t\) | \(-D-5\) | \(2D+2r+14\) | \(2r+4\) |
| LE | \(d\) even, \(a=d+2+k+t\) | \(-D-2\) | \(2D+2r+8\) | \(2r+4\) |
| RO | \(d\) odd, \(d=a+1+2k+2t\) | \(4-D\) | \(2D+2r\) | \(2r+8\) |
| RE | \(d\) even, \(d=a+2+2k+2t\) | \(-D\) | \(2D+2r+7\) | \(2r+7\) |

These identities are the exact drain normal form and the four weighted correction identities written in a common pair of statistics. They do not assume an asymptotic approximation.

## Exact output-side decision

The output is \(D(A,E)\), where the affine shift contributes \(t\) to the first output counter in LO/LE and \(2t\) in RO/RE. Direct subtraction gives:

| Input sector | \(A-E\) | Output orientation |
|---|---:|---|
| LO | \(g-3D-2r-19\) | left iff \(g\ge 3D+2r+19\) |
| LE | \(g-3D-2r-10\) | left iff \(g\ge 3D+2r+10\) |
| RO | \(g-3D-2r+4\) | left iff \(g\ge 3D+2r-4\) |
| RE | \(g-3D-2r-7\) | left iff \(g\ge 3D+2r+7\) |

Otherwise the output is right. This is an exact decision criterion; it avoids assuming that the output orientation is determined by the sign of \(g\).

## Exact gap/scale update

The canonical-ray source gives, according to the output orientation,
\[
\begin{array}{ll}
\text{left output:}&
g'=g-9m+\beta-4\delta,\quad m'=3m+\delta,\\[2mm]
\text{right output:}&
g'=-4g-9m+\delta-4\beta,\quad m'=g+3m+\beta.
\end{array}
\]
Substitution of the two-statistic correction table yields all eight exact cases:

| Input sector | Output | \(g'\) | \(m'\) |
|---|---|---|---|
| LO | left | \(g-9m-9D-8r-61\) | \(3m+2D+2r+14\) |
| LO | right | \(-4g-9m+6D+2r+34\) | \(g+3m-D-5\) |
| LE | left | \(g-9m-9D-8r-34\) | \(3m+2D+2r+8\) |
| LE | right | \(-4g-9m+6D+2r+16\) | \(g+3m-D-2\) |
| RO | left | \(g-9m-9D-8r+4\) | \(3m+2D+2r\) |
| RO | right | \(-4g-9m+6D+2r-16\) | \(g+3m+4-D\) |
| RE | left | \(g-9m-9D-8r-28\) | \(3m+2D+2r+7\) |
| RE | right | \(-4g-9m+6D+2r+7\) | \(g+3m-D\) |

The output parity is fixed by the input sector: LO gives odd E, LE gives even E, RO gives even E, and RE gives odd E.

## Exact recurrence for the branch-specific terminal distance

Combining the preceding update with the parity-dependent definition of \(h\) gives the following exact recurrence. The output column is selected by the exact \(A-E\) test above.

| Input sector | Output left: \(h'\) | Output right: \(h'\) |
|---|---|---|
| LO | \(h-9m-9D-8r-61\) | \((-4h-9m+6D+2r-3)/2\) |
| LE | \(h-9m-9D-8r-34\) | \((-4h-9m+6D+2r-6)/2\) |
| RO | \(2h-9m-9D-8r\) | \((-8h-9m+6D+2r-22)/2\) |
| RE | \(2h-9m-9D-8r-35\) | \((-8h-9m+6D+2r-2)/2\) |

The numerators in the right-output cases are even by the source parity constraints.

Reducing this recurrence modulo \(3\) gives a compact low-digit update:
\[
h'\equiv
\begin{cases}
h+r-1 & \text{LO/LE, output left},\\
h+r & \text{LO/LE, output right},\\
2h+r & \text{RO, output left},\\
2h+r+1 & \text{RO, output right},\\
2h+r+1 & \text{RE, output left},\\
2h+r+2 & \text{RE, output right}
\end{cases}
\pmod3.
\]
The statistic \(r\) remains a drain digit statistic; this is an exact recurrence, not yet a closed finite-state evolution on \(h\) alone.

## Why this is useful for the root problem

The terminal-ratio theorem bounds the branch-specific distance \(h\) by a logarithmic window. The recurrence above supplies the exact transition of that same \(h\), including the output-side decision, without relying on the finite-scan observation that side selection happens to agree with the sign of \(g\).

This is the algebraic input needed to revisit the 3-adic residue-separation observation in communications/agent41/20261117T074927Z_agent32-3adic-terminal-residue-observation.md. The remaining difficulty is to control \(D,r\) along the authentic \(D(0,7)\) orbit strongly enough to prove that the residue of \(h\) modulo a growing power of \(3\) cannot enter the full logarithmic terminal window.

No blank-root reachability claim is made here. The formulas follow by substitution from DrainValuationNormalForm.md, ExactRayCorrectionRelations.lean, and the canonical-ray gap/scale update.
