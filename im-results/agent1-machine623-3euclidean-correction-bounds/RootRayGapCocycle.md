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
- \(D\): the signed first-counter drop from the sector's canonical baseline. The baselines are \(k\) in LO/LE, \(2k+5\) in RO, and \(2k+3\) in RE, so the final base first counter is baseline minus \(D\);
- \(r\): the number of outer drain iterations.

For LO, LE, and RO, \(D=L-2e\) in the valuation normal form, where \(L\) is the valuation-run length and \(e\) counts the terminal-digit-2 cases. For RE, \(D\) is measured from the initial evalA first counter \(2k+3\): it is the initial evalA drop (including its terminal-digit adjustment) plus the subsequent drain drop. In every sector, \(r\) is the outer drain iteration count appearing in the exact weighted correction identity.

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
| RE | \(d\) even, \(d=a+2+2k+2t\) | \(1-D\) | \(2D+2r+5\) | \(2r+7\) |

These identities are the exact drain normal form and the four weighted correction identities written in a common pair of statistics. They do not assume an asymptotic approximation.

## Exact output-side decision

The output is \(D(A,E)\), where the affine shift contributes \(t\) to the first output counter in LO/LE and \(2t\) in RO/RE. Direct subtraction gives:

| Input sector | \(A-E\) | Output orientation |
|---|---:|---|
| LO | \(g-3D-2r-19\) | left iff \(g\ge 3D+2r+19\) |
| LE | \(g-3D-2r-10\) | left iff \(g\ge 3D+2r+10\) |
| RO | \(g-3D-2r+4\) | left iff \(g\ge 3D+2r-4\) |
| RE | \(g-3D-2r-4\) | left iff \(g\ge 3D+2r+4\) |

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
| RE | left | \(g-9m-9D-8r-19\) | \(3m+2D+2r+5\) |
| RE | right | \(-4g-9m+6D+2r+1\) | \(g+3m+1-D\) |

The output parity is fixed by the input sector: LO gives odd E, LE gives even E, RO gives even E, and RE gives odd E.

## Exact recurrence for the branch-specific terminal distance

Combining the preceding update with the parity-dependent definition of \(h\) gives the following exact recurrence. The output column is selected by the exact \(A-E\) test above.

| Input sector | Output left: \(h'\) | Output right: \(h'\) |
|---|---|---|
| LO | \(h-9m-9D-8r-61\) | \((-4h-9m+6D+2r-3)/2\) |
| LE | \(h-9m-9D-8r-34\) | \((-4h-9m+6D+2r-6)/2\) |
| RO | \(2h-9m-9D-8r\) | \((-8h-9m+6D+2r-22)/2\) |
| RE | \(2h-9m-9D-8r-26\) | \((-8h-9m+6D+2r-8)/2\) |

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


## A middle-block certificate for 3-adic separation

Let \(W\ge1\), let \(k\) be least with \(3^k>W\), and let \(j\) be least with \(3^j>W^3\). Then
\[
3^{3(k-1)}\le W^3<3^j,
\]
so \(j\ge3k-2\).

For an integer \(z\), let \(r\) be the least nonnegative residue of \(z\) modulo \(3^j\). Consider the block of base-3 digits of \(r\) in positions \(k,\ldots,j-1\). If this block is **neither all zero nor all two**, then
\[
\min(r,3^j-r)>W.
\]
Indeed, if the block is not all zero, some digit at position \(i\ge k\) is nonzero, so \(r\ge3^i\ge3^k>W\). If the block is not all two, some digit at position \(i\ge k\) is at most one; subtracting \(r\) from \(3^j\) then gives \(3^j-r\ge3^i\ge3^k>W\). The single-middle-digit-1 criterion is a special case, but a mixed block of zeros and twos also suffices.

Thus a finite-state proof of residue separation can target the weaker-looking digit statement that the middle block is not monochromatic (all zero or all two), rather than directly proving a least-residue inequality. In a 100-state arithmetic diagnostic of the authentic root, using \(W=9\ell+22\) and the corresponding \(k,j\), this block was not all zero and not all two for every tested state from index 17 through 99; index 16 was the only failure, and there \(\min(r,3^j-r)=73\le W=76\). This is finite computational evidence only, not an all-time invariant.


## Bridge to the terminal-window width used by the 3-adic scan

For the canonical band parameter \(n\) used by RootCancellationExponentTransfer, the hypotheses are
\[
3^{n-1}-3\le q,\qquad q+3<3^n,\qquad n\ge10.
\]
Let \(\ell\) be least with \(\tau(\ell)=(3^\ell-1)/2\ge q+3\), as in Agent32's residue scan. Then
\[
n\le\ell\le n+1.
\]
Indeed, \(q+3\ge3^{n-1}>\tau(n-1)\), so \(\ell\ge n\); and \(\tau(n+1)>3^n>q+3\), so \(\ell\le n+1\).

The terminal-ratio bounds with \(K=n+6\), converted to the old-ray distances above, are bounded in every sector by \(9n+22\) for \(n\ge10\):
- LO: \(|h|\le 6n+44\le9n+22\);
- LE: \(|h|\le 6n+31\le9n+22\);
- RO: \(|h|\le(6n+19)/2\le9n+22\);
- RE: \(|h|\le(9n+25)/2\le9n+22\).

Consequently Agent32's \(W=9\ell+22\) is a conservative common terminal-window envelope for the source-supported n>=10 regime. This aligns the 3-adic residue target with the source terminal-ratio theorem. It does not cover the n<10 small-depth regime, which remains a separate root-prefix obligation.


### Right-even baseline normalization (correction)

The RE row above uses the initial evalA first counter \(2k+3\) as its baseline. If \(D\) is the total signed first-counter drop from that baseline, then \(B=2k+3-D\), so \(\beta=B-2-2k=1-D\). The exact weighted identity \(\delta+2\beta=2r+7\) then gives \(\delta=2D+2r+5\). This convention is preferable to measuring \(D\) from the shifted baseline \(2k+2\), because it makes \(D\) the actual initial-evalA drop plus the later drain drop and gives the uniform digit-depth bound \(|D|\le\ell+1\) when the two consumed ternary blocks are combined.


## Sharpened exact predecessor strips from the two-statistic cocycle

The drain normal form also gives a uniform depth bound for the statistics above. Let \(\ell\) be least with \(\tau(\ell)\ge q+3\), where \(q=m\) is the smaller current counter.
- In LO/LE/RO, the drain block \(b\) satisfies \(b\le q+3\). Hence \(2b-1<3^\ell\). The parity-matched valuation length is at most \(\ell+1\); its ternary normal-form integer has fewer than \(3^{\ell+1}\) and at most \(\ell+1\) digits. Therefore \(|D|\le\ell+1\) and \(r\le\ell\).
- In RE, let \(v\) be the initial low-order-1 run consumed by evalA. Its signed first-counter drop from baseline \(2k+3\) is \(v+1-2\varepsilon\), of absolute value at most \(v+1\). The remaining quotient has valuation length \(L_2\le\ell-v\): this follows from \(2q-1<3^\ell\) after removing the \(v+1\) consumed ternary positions, with at most one extra exponent for the parity match. Thus \(|D|\le v+1+L_2\le\ell+1\) and \(r\le L_2\le\ell\). The cone budget ensures the initial evalA run succeeds rather than taking its early-exit branch.

Now suppose the output state is in the source terminal window. The TerminalRatio4 bounds with \(K=n+6\), translated to the old-ray distance, are:
\[
W_{\rm LO}=6n+44,\quad
W_{\rm LE}=6n+31,\quad
W_{\rm RO}=(6n+19)/2,\quad
W_{\rm RE}=(9n+25)/2.
\]
Using the exact \(h'\) table, a left output gives a predecessor far residual \(u=g-9m\), while a right output gives a predecessor near residual \(v=4g+9m\). Substituting \(|D|\le\ell+1\), \(r\le\ell\), and \(\ell\le n+1\) gives:

| Input sector | Output | Predecessor residual | Absolute bound |
|---|---|---|---:|
| LO | left | \(g-9m\) | \(23n+140\) |
| LO | right | \(4g+9m\) | \(20n+135\) |
| LE | left | \(g-9m\) | \(23n+96\) |
| LE | right | \(4g+9m\) | \(20n+90\) |
| RO | left | \(g-9m\) | \(20n+37\) |
| RO | right | \(4g+9m\) | \(14n+51\) |
| RE | left | \(g-9m\) | \(22n+67\) |
| RE | right | \(4g+9m\) | \(17n+39\) |

Thus every terminal event with canonical depth \(n\ge10\) has a predecessor in one of the two strips
\[
|g-9m|\le 23n+140
\quad\text{or}\quad
|4g+9m|\le 23n+140.
\]
This improves the common \(35n+120\) envelope in RootCancellationBudgetBridge.md for \(n\ge10\), since \(23n+140<35n+120\) whenever \(n\ge3\). The gain comes from keeping the exact sector-specific \(D,r\) coefficients instead of bounding the two bridge corrections independently.

This is still a necessary-condition theorem, not an exclusion of the authentic root from these strips. It should be consumable by the existing root mass-corridor / checkpoint-gap method.


### Formalization status of the depth bound

The RE initial-run formula uses Agent41's source-compiled evalA_3adic_run theorem. The remaining drain depth estimates can be packaged from the current Lean drafts:
- Agent49 DrainLinearLogSource.drainB_first_lower_log / drainB_first_upper_log bound the signed first-counter drop;
- Agent22 ExactDrainCocycleDepthSource.drainB_weighted_depth bounds the outer iteration count.
Those draft modules are not both included in the existing pinned source-CI workflows yet. Therefore the numerical strip table above is an exact derivation from the stated lemmas, but the combined \(|D|,r\le\ell+1\) wrapper and the sharpened 23n+140 strip have not yet been source-CI certified. Do not describe them as fully formalized until that wrapper is compiled against the pinned original machine.


### Iteration-count refinement

The outer-count estimate can be sharpened from \(r\le\ell+1\) to \(r\le\ell\). For LO/LE/RO, the drain block \(b<3^\ell\), so Agent22's drainB_weighted_depth lemma gives \(r\le\ell\). In RE, after the initial \(v+1\) evalA digits, the residual block is \(b_0<3^{\ell-v-1}\), so the same lemma gives \(r\le\ell-v-1\le\ell\). The signed first-counter bound remains \(|D|\le\ell+1\). This tightens the common predecessor strip to \(23n+140\).


### Observed two-digit-buffer refinement (candidate invariant)

A second diagnostic tracked the same nonmonochromatic condition simultaneously for \(h\) and \(m\), after trimming two digits from both ends of the middle block. On the 100-state root replay, both trimmed blocks were nonmonochromatic at every tested index \(30,\ldots,99\); the only trimmed-block exceptions in the earlier prefix occurred at indices 17–29. Trimming two positions is natural for the exact cocycle because the largest explicit 3-adic shift in the left branch is \(9m\), and the right branch also has coefficients divisible by \(9\) on the scale term.

This suggests a possible finite-state induction target: after a separately certified finite prefix, maintain a two-digit-buffer nonmonochromatic property for the pair \((h,m)\). It is only a candidate invariant; the 100-state replay is not proof, and preservation under all four sector transitions still needs to be established.


The buffer has a carry interpretation. A nonzero digit in the high block ensures the residue is not small; a digit different from two ensures its complement is not small. Addition can carry upward only through a run of twos, while subtraction can borrow upward only through a run of zeros. Thus a block containing both a nonzero digit and a digit below two stops both kinds of carry. The exact cocycle's explicit corrections are \(O(\ell)\), while \(3^{k+2}>9W\) and \(W=9\ell+22\); the largest linear shift is \(9m\), i.e. two ternary places. This explains why trimming two low/high positions is a natural candidate buffer. The remaining proof obligation is to show that the four integer linear transformations on \((h,m)\), together with their finite carry states, preserve a suitable nonmonochromatic block language.


## Compact absolute-value cocycle

Agent 3 supplied a useful all-sector compression of the eight cases. Put \(p=|a-d|\), \(q=\min(a,d)=m\), \(g=p-3q\), and
\[
T=\delta-\beta=3D+2r+c_s,\qquad
c_s=\begin{cases}19&\mathrm{LO}\\10&\mathrm{LE}\\-4&\mathrm{RO}\\4&\mathrm{RE}.\end{cases}
\]
The two counters before sorting are exactly \(A=p+\beta\) and \(E=3q+\delta\). Hence
\[
\boxed{p'=|g-T|,\qquad q'=\min(p+\beta,\,3q+\delta).}
\]
The output-side decision is exactly the sign of \(g-T\); no sector-specific orientation guess is needed.

With \(Y=2g\), this becomes the single gap/scale identity
\[
\boxed{Y'=|Y-2T|-6q'.}
\]
This follows by considering the sign of \(g-T\) in the preceding \(p',q'\) formula, and is equivalent to all eight exact \((g',m')\) updates.

A second coordinate \(X=2g+9m=2p+3q\) has an especially simple update. Let \(S=\delta+2\beta\). Then
\[
S=\begin{cases}
2r+4&\mathrm{LO/LE},\\
2r+8&\mathrm{RO},\\
2r+7&\mathrm{RE}.
\end{cases}
\]
For left output, \(X'=X+S\), so both \(D\) and the old scale cancel. For right output,
\[
2X'=X+9m+3\delta+S.
\]
The factor \(9m\) is the explicit two-place ternary shift; the only remaining drain dependence is through \(\delta\) and \(S\).

The old-ray distance is an affine rescaling of \(Y\):
\[
Y=2h+18\ (\mathrm{LO}),\quad
Y=2h+10\ (\mathrm{LE}),\quad
Y=4h+2\ (\mathrm{RO}),\quad
Y=4h+4\ (\mathrm{RE}).
\]
Thus a terminal window \(|h|\le W\) is a short interval for \(Y\) centered at 18, 10, 2, or 4, with radius \(2W\) or \(4W\). This may be a better coordinate for a finite-state 3-adic transducer than carrying the four separate \(h'\) formulas.

Normalization reminder: in RE, \(D\) includes the initial evalA first-counter drop from baseline \(2k+3\) plus the subsequent drain drop, while \(r\) counts only the subsequent outer drain iterations. If the initial evaluator is bundled into a single drain count \(R\), then \(r=R-1\). This is consistent with \(\beta=1-D\), \(\delta=2D+2r+5\), and \(S=2r+7\).


### Centered-\(Y\) residue diagnostic

The compact coordinate gives a second way to formulate the terminal window. Let \(c_s=18,10,2,4\) in LO/LE/RO/RE and set \(z=Y-c_s\). Then \(z=2h\) in LO/LE and \(z=4h\) in RO/RE, so \(|h|\le W\) implies \(|z|\le4W\) uniformly. Using \(W_Y=4W\), and defining \(k,j\) by \(3^k>W_Y\), \(3^j>W_Y^3\), the same middle-block criterion applies to \(z\bmod3^j\).

On the same 100-state diagnostic, this centered-\(Y\) middle block was neither all zero nor all two at every tested index 17–99; index 16 was the only failure. The \(Y\)-form may be better suited to a transducer proof because the exact update is the single absolute-value recurrence \(Y'=|Y-2T|-6q'\). This is finite computational evidence only.


For the centered-\(Y\) window in the source regime \(n\ge10\), \(\ell\ge n\ge10\), so \(W_Y=4(9\ell+22)\ge448>3^5\), hence \(k\ge6\). Since \(j\ge3k-2\), the two-digit-buffer interior \([k+2,j-2)\) has length
\[
j-k-4\ge2k-6\ge6.
\]
Thus the proposed buffered invariant has at least six ternary positions throughout the n>=10 regime; it does not collapse to a vacuous short block.


A further buffer test on the centered-\(Y\) residual \(z=Y-c_s\), using the uniform width \(W_Y=4W\), found that the middle block trimmed by two positions at each end was nonmonochromatic at every tested index \(33,\ldots,99\). The trimmed-block failures in the tested prefix were indices 17–32. This suggests a finite prefix through 32 followed by a buffered \(Y\)-invariant, but remains only a 100-state diagnostic.


### Explicit lemma chain for the D/r wrapper

The intended Lean wrapper can avoid reproving the drain recursion:
1. For LO/LE/RO, \(b\le q+3\le\tau(\ell)<3^\ell\). Apply Agent49's draft drainB_first_lower_log and drainB_first_upper_log with exponent \(\ell\) to the successful drain output. They give \(-\ell\le D\le\ell+1\). Apply Agent22's drainB_weighted_depth with the same exponent to get \(r\le\ell\).
2. For RE, write the small counter's ternary decomposition as \(q=\tau(v)+3^v(3b_0+1+\varepsilon)\), with \(\varepsilon\in\{0,1\}\). Agent41's source-compiled evalA_3adic_run gives the initial first-counter drop \(D_0=v+1-2\varepsilon\) and residual block \(b_0\). The canonical cone budget \(q<\tau(2k+3)\) implies \(v+1-\varepsilon\le2k+3\), so the success hypothesis of that theorem holds. From \(q+3\le\tau(\ell)\), obtain \(b_0<3^{\ell-v-1}\) whenever \(b_0>0\). If \(b_0=0\), the residual drain is empty and \(D_2=r=0\); otherwise \(v+1<\ell\), so the exponent is nonnegative. Apply the two Agent49 first-counter logarithmic bounds to the residual drain with exponent \(\ell-v-1\), giving \(|D_2|\le\ell-v\); apply Agent22's weighted-depth lemma to get \(r\le\ell-v-1\). Since \(D=D_0+D_2\), \(|D|\le v+1+\ell-v=\ell+1\), and \(r\le\ell\).
3. Substitute these inequalities and the four source terminal windows into the exact cocycle identities to obtain the \(23n+140\) predecessor strips.

The only non-source-CI pieces in this chain are the Agent49/Agent22 draft wrappers; the evalA success normal form itself has its existing source workflow. This is the minimal batch that needs to be added to a pinned source-CI job.


## D-free sector-adapted coordinate

Agent 3 found a further simplification. Put \(K=2p+3q\), \(S=\delta+2\beta=2r+c_s\), with \(c_s=4,4,8,7\) in LO/LE/RO/RE. Let \(\epsilon=0\) for a left-oriented input and \(\epsilon=1\) for a right-oriented input, and define
\[
H=K+3\epsilon q.
\]
Let \(\lambda=1\) for a left output and \(\lambda=2\) for a right output. Since \(K'=K+S\) on left output and \(K'+3q'=2(K+S)\) on right output, the next sector-adapted coordinate satisfies the single exact identity
\[
\boxed{H'=\lambda(H-3\epsilon q+S),\qquad S=2r+c_s.}
\]
The next state's orientation is exactly the output orientation, so this definition is consistent across transitions.

Moreover \(H\equiv K\equiv2p\pmod3\), hence
\[
H'\equiv\lambda(H+2r+c_s)\pmod3.
\]
The signed drop \(D\) disappears completely from the H update; the old scale enters only as the one-place shifted term \(3q\) on right-oriented inputs. This is a promising coordinate for a 3-adic transducer. The terminal residual remains \(Y=2g=H-3(3+\epsilon)q\), so the root proof must still control the joint pair \((H,q)\), but the H dynamics are simpler than the original eight h' formulas.


### Terminal strips in the D-free coordinate

Since \(Y=H-3(3+\epsilon)q\), the source terminal windows become direct linear strips in \((H,q)\):
\[
\begin{array}{ll}
\mathrm{LO}:&|H-9q-18|\le 12n+88,\\
\mathrm{LE}:&|H-9q-10|\le 12n+62,\\
\mathrm{RO}:&|H-12q-2|\le 12n+38,\\
\mathrm{RE}:&|H-12q-4|\le 18n+50.
\end{array}
\]
Here the four widths are \(2W_{\rm LO}\), \(2W_{\rm LE}\), \(4W_{\rm RO}\), and \(4W_{\rm RE}\) from TerminalRatio4. Meanwhile the D-free H update is \(H'=\lambda(H-3\epsilon q+2r+c_s)\); \(D\) affects only the branch choice through the sign of
\[
H-3(3+\epsilon)q-6D-4r-2c_s.
\]
This separates the size update from the signed-drop statistic and may be useful for a joint modular exclusion of the four terminal strips.


## 2026-11-18 normalization: one full-drain count

The preceding derivation uses a split convention: in LO/LE/RO, (r) is the number of calls in the drain; in RE, (r) excludes the initial evaluator. The RE baseline for (D) is already the full initial evaluator input (2k+3), so (D) does include the initial evaluator's first-counter drop.

For a uniform convention, define (R) to be the total number of evaluator calls in the complete drain. Then
[
R=rquad	ext{in LO/LE/RO},qquad R=r+1quad	ext{in RE}.
]
Thus the RE identities in the preceding sections must be rewritten by substituting (r=R-1). In particular,
[
eta=1-D,qquad
delta=2D+2R+3,qquad
S=delta+2eta=2R+5,
]
and
[
T=delta-eta=3D+2R+2.
]
The RE gap/scale updates become
[
egin{aligned}
g'_L&=g-9m-9D-8R-11,\
g'_R&=-4g-9m+6D+2R-1,\
m'_L&=3m+2D+2R+3,\
m'_R&=g+3m+1-D.
end{aligned}
]
The sector constants in the uniform notation are therefore
[
S=2R+c_s,quad c_s=(4,4,8,5),
qquad
T=3D+2R+c_T,quad c_T=(19,10,-4,2)
]
in LO/LE/RO/RE respectively. In particular, the D-free coordinate update is now
[
H'=\lambda(H-3\epsilon q+2R+c_s).
]

The full-drain correction table in [SignedCoordinateNormalForm.md](SignedCoordinateNormalForm.md) uses this uniform (R) convention. Its RE constants differ from the split-(r) formulas above by exactly the substitution (r=R-1). The source-compiled right-even depth wrapper in Agent8's successful agent8-623-third-affine run packages the initial evaluator into the same drain call; this normalization does not, by itself, prove the root nonhalting theorem.
