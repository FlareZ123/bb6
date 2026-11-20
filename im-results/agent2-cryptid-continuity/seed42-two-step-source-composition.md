# Seed42 two-step original-source composition

**Status:** proof-ready composition of existing original-source theorems; the combined Lean wrapper has not yet been compiled or axiom-audited. This belongs in im-results, not results. It is not a blank-root reachability theorem.

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

The universal theorem BB6.Agent31RegularELow.e_zero_suffix states
\[
\operatorname{ObsEq}\left(
  \operatorname{run}(12p^2+49p+50+4q,\operatorname{sourceSection}(3p+4,q,0)),
  \operatorname{sourceSection}(8p+5,1,2q+5)
\right).
\]
Specializing \(q=4\) gives
\[
L(3p+4,4,0)
\xrightarrow{12p^2+49p+66}
L(8p+5,1,13)
=L(32768s+31069,1,13).
\]
The lemma is already an original-machine physical-tape result: it uses explicit far-blank padding and ObsEq, not the arithmetic L-table alone.

## Second source return: split on the next ternary digit

Write \(s=3r+i\), \(i\in\{0,1,2\}\). The middle index is
\[
a_1=32768(3r+i)+31069.
\]

### \(i=0\): E row

\[
a_1=98304r+31069=3k_0+4,\quad k_0=32768r+10355.
\]
The universal original-source contract
BB6.Agent31RegularE.e_contract_many applies because \(q=1>0\) and \(b=13\ge3\). Its DRegular.next target is
\[
L(8k_0+9,3,10)=L(262144r+82849,3,10).
\]

### \(i=1\): A row

\[
a_1=98304r+63837=3k_1+3,\quad k_1=32768r+21278.
\]
The universal A source contract
BB6.ARegularFull.original_A_positive_row applies because \(q=1>0\). In the A row, \(b+1=14\), \(r_b=(b+1)/3=4\), and
\[
d=(q-1)+4r_b=16.
\]
The model successor is \(L(8k_1+7+2d,1,5)=L(8k_1+39,1,5)\), hence
\[
L(262144r+170263,1,5).
\]

### \(i=2\): B row

\[
a_1=98304r+96605=3k_2+2,\quad k_2=32768r+32201.
\]
The universal original-source contract
BB6.BRegularSource.original_B_row applies. Since \(q=1\), the B-one row merges the remaining \(b=13\) ones into the unary prefix:
\[
L(8k_2+10+13,0,0)=L(8k_2+23,0,0)
=L(262144r+257631,0,0).
\]

All three targets are canonical: the first two have positive \(q\), while the B target has \(q=b=0\).

## Exact composition argument

For each \(i\), let \(C\) be the first seed configuration, \(M_i\) the corresponding middle state, and \(T_i\) the target above. The first theorem gives
\[
\operatorname{ObsEq}(\operatorname{run}(t_1,C),M_i).
\]
The selected universal A/E/B contract gives
\[
\operatorname{ObsEq}(\operatorname{run}(t_{2,i},M_i),T_i);
\]
the E contract is an exact configuration equality and is converted to reflexive ObsEq. Then
BB6.BoundaryPadding.source_chain yields
\[
\operatorname{ObsEq}(\operatorname{run}(t_1+t_{2,i},C),T_i).
\]
Thus the two-step family is not merely an arithmetic-model prediction. It is a direct composition of existing source-level certificates.

## Dependencies and limitations

- First step: im-results/agent31-d-exceptional/DRegularELow.lean, theorem e_zero_suffix.
- E branch: im-results/agent31-d-exceptional/DRegularESource.lean, theorem e_contract_many.
- A branch: restored from im-results/agent2-cryptid-continuity/ARegularSourceBundle.tar.xz.b64, theorem BB6.ARegularFull.original_A_positive_row.
- B branch: im-results/agent2-cryptid-continuity/BRegularSource.lean, theorem original_B_row.
- Composition: im-results/agent32-cryptid-padding/BoundaryPadding.lean, theorem source_chain.

The next implementation task is a small Lean wrapper importing these four modules, proving the three concrete DRegular.next equations by arithmetic simplification, and invoking source_chain for each residue. Its imports must be compiled against the restored, SHA-pinned source dependencies. The current invocation's local shell and Python execution tools failed before executing even trivial commands, so no local preflight was possible; no CI run is being substituted for that required preflight.

**Crucial scope:** \(L(12288s+11653,4,0)\) is a conditional prepared seed. This result does not prove the blank-tape trajectory reaches it. The Seed39 first-stop bound, the additional \(s\bmod3\) digit, and the upstream blank-root composition remain unresolved.
