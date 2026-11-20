# Seed42 two-step original-source composition

**Status:** proof-ready composition using the existing universal original-source contract; the combined Lean wrapper has not yet been compiled or axiom-audited. This is intermediate research in im-results, not an academically publishable result or a blank-root reachability theorem.

## Input seed

The conditional normalizer endpoint is
\[
L(12288s+11653,4,0),\qquad s\in\mathbb N.
\]
Set \(p=4096s+3883\). Then
\[
12288s+11653=3p+4.
\]

## First source return

The explicit universal E-low theorem BB6.Agent31RegularELow.e_zero_suffix specializes at q=4 to
\[
L(3p+4,4,0)
\xrightarrow{12p^2+49p+66}
L(8p+5,1,13)
=L(32768s+31069,1,13).
\]
It gives physical ObsEq and exposes the primitive time. The same transition is also covered by the stronger universal source contract below.

## Universal source contract

DObsSourceCandidate.lean defines
\[
\begin{aligned}
\text{SourceContract} \;:\!\!\iff\;&
\forall s,t,\; DRegular.Canon(s)\to DRegular.next(s)=\operatorname{some}(t)\\
&\to \operatorname{ObsEq}(
  \operatorname{run}(DRegular.duration(s),\operatorname{sourceSection}(s)),
  \operatorname{sourceSection}(t)).
\end{aligned}
\]
The restored module ERemaining proves
BB6.ERemaining.source_contract : DRegularSource.SourceContract
for all eleven successful canonical DRegular rows against the unchanged original machine source. Its complete original-source CI audit succeeded in
[run 41712102615](https://github.com/FlareZ123/bb6/actions/runs/41712102615);
the transitive axiom list is only propext, Classical.choice, and Quot.sound.
Consequently, each transition below is obtained by proving Canon and the
concrete DRegular.next equation, then applying this one contract. Separate
A-, B-, and E-row theorem imports are unnecessary.

## Second source return: split on the next ternary digit

Write \(s=3r+i\), \(i\in\{0,1,2\}\). The middle index is
\[
a_1=32768(3r+i)+31069.
\]

### \(i=0\): E row

\[
a_1=98304r+31069=3k_0+4,\quad k_0=32768r+10355.
\]
The E row of DRegular.next yields
\[
L(8k_0+9,3,10)=L(262144r+82849,3,10).
\]

### \(i=1\): A row

\[
a_1=98304r+63837=3k_1+3,\quad k_1=32768r+21278.
\]
Here \(b+1=14\), \((b+1)/3=4\), and
\[
d=(q-1)+4((b+1)/3)=16.
\]
The A row target is \(L(8k_1+7+2d,1,5)=L(8k_1+39,1,5)\), hence
\[
L(262144r+170263,1,5).
\]

### \(i=2\): B row

\[
a_1=98304r+96605=3k_2+2,\quad k_2=32768r+32201.
\]
The B-one row merges the remaining \(b=13\) ones into the unary prefix:
\[
L(8k_2+10+13,0,0)=L(8k_2+23,0,0)
=L(262144r+257631,0,0).
\]

All three targets are canonical: the first two have positive q, while the B target has q=b=0.

## Exact composition argument

For each i, let C be the first seed configuration, M_i the corresponding middle state, and T_i the target above. The explicit E-low theorem gives
\[
\operatorname{ObsEq}(\operatorname{run}(t_1,C),M_i).
\]
The universal ERemaining source contract gives
\[
\operatorname{ObsEq}(\operatorname{run}(t_{2,i},M_i),T_i).
\]
Then BB6.BoundaryPadding.source_chain yields
\[
\operatorname{ObsEq}(\operatorname{run}(t_1+t_{2,i},C),T_i).
\]
The first time is \(t_1=12p^2+49p+66\); the second time is
\(t_{2,i}=DRegular.duration(M_i)\).

Thus the two-step family is a direct composition of existing
original-source certificates, not merely an arithmetic-model prediction.

## Dependencies and limitations

- First-step explicit cost: im-results/agent31-d-exceptional/DRegularELow.lean, theorem e_zero_suffix.
- Universal eleven-row contract: restored ERemaining.lean, produced by restore_e_regular.py, with the source definition in im-results/agent35-d-regular-certificate/DObsSourceCandidate.lean.
- Composition: im-results/agent32-cryptid-padding/BoundaryPadding.lean, theorem source_chain.

The next implementation task is a small Lean wrapper importing ERemaining and
BoundaryPadding, proving the four concrete DRegular.next equations
(first step plus three second-step residues), and invoking source_chain for
each residue. The archived ERemaining module must be restored using the
pinned restore script and exact source snapshot. The current invocation's
local shell and Python execution tools failed before executing even trivial
commands, so no local preflight was possible; no CI run is being substituted
for that required preflight.

**Crucial scope:** \(L(12288s+11653,4,0)\) is a conditional prepared seed. This result does not prove the blank-tape trajectory reaches it. The Seed39 first-stop bound, the additional \(s\bmod3\) digit, and the upstream blank-root composition remain unresolved.
