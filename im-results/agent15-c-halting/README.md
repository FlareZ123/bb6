# Machine C: exact section halting locus and affine inverse normalizer

**Research state (6 November 2026): a complete algebraic stopping-locus description with source-connected reductions and separate verification boundaries for later compositions; Machine C and BB(6) remain unresolved.** [Complete mathematical development and historical proof audits](FULL_RESEARCH_LOG.md).

## Section stopping semantics

The authentic Machine C accelerated section begins at `(5,1)` with `BB6.Agent46.secNext`. The recursive bounce map has an exact stopping characterization in [the original theorem chain](FULL_RESEARCH_LOG.md): for `c≥4`, `bounce(k,c).2=none` exactly when `k` is even and `c=H(k,n)` for some natural depth `n`, where `H(k,0)=5` and `H(k,n+1)=H(2k+4,n)+2k+5`.

The stronger parity-normalized original-root gateway, modular quotient exclusions and [AffineParityDepth.lean](AffineParityDepth.lean) reduce which stopping inputs can be reached. Exact normalizer identities include `x+2y+4*oddDepth(k)=a+2k` and `2^oddDepth(k)*(y+2)=k+2` for the normalized source pair `(x,y)`.

## Provenance boundaries

The dossier distinguishes the copied-definition/local Lean checks, original `CLine` quotient imports, and later source-composition modules. Earlier `M8M16Composition.lean` CI exposed an iterator bridge error, which was repaired using the existing `BB6.Agent46.run_eq` theorem. Individual later modules should be cited only with the exact successful original-source CI that checked their version. The [Machine C combined true-root theorem](../agent19-c-odd-dyadic/JointAllRoot.lean) is a more useful current entry point for the remaining global condition.

## Exact modular classification and density of one M8 quotient-parity cylinder

[Arithmetic classification and density proof](M8HighDensity.md). At each positive odd second-family index `m` and every compatible depth `d`, the forbidden quotient-parity condition corresponds to exactly one `j` residue modulo `2^(d+3)`, explicitly `j ≡ Q⁻¹(m+2^(d+1))−3`, with `Q=(2^(2m+2)−1)/3`. Distinct depths give disjoint classes. Summing the progressions yields natural density **1/12** when `m%4=1` and **1/24** when `m%4=3`. This precise claim describes only this one M8 cylinder, and the arithmetic inverse/density components are currently paper proofs rather than independent Lean theorems. The source-level exclusion implication is [formalized here](M8GenericHigh.lean), with source-closure CI pending.

## All-odd M8 towers at arbitrarily high normalizer depth

[General mathematical construction and exact proof boundary](M8OddTower.md). The newer theorem [M8OddTower.lean](M8OddTower.lean) expands the single-depth result below to **every odd stopping-family index `m` and every positive tower height `r`**, giving a source-excluded infinite progression of stopping inputs with exact normalizer depth `r*(2*m+2)+1` or `r*(2*m+2)`. [M8OddTowerPrior.lean](M8OddTowerPrior.lean) proves the construction is outside every residue tested by the earlier dyadic-tower sieve. [M8OddTowerStructure.lean](M8OddTowerStructure.lean) proves distinct levels cannot share any right coordinate and calculates the exact progression step. [M8GenericHigh.lean](M8GenericHigh.lean) gives a reusable all-depth Diophantine exclusion theorem that covers other parameterizations. Local Lean 4.36.0-rc2 compiles all theorem bodies without `sorryAx` against source-signature stubs; [original-source CI](https://github.com/FlareZ123/bb6/actions/runs/45099456878) has been dispatched and its result determines whether to promote any source-level claim. This does not establish Machine C nonhalting or BB(6).

## Deep M8 forbidden stopping families for every odd index

[Construction, examples, proof boundary and comparison to earlier filters](M8OddDeep.md). The source bodies in [M8OddDeep.lean](M8OddDeep.lean) prove, modulo the previously established M8 quotient and affine source theorems, an explicit infinite high-stopping exclusion for **every positive odd** second-family index `m`. The normalizer depth is `2*m+3` when `m%4=1` and `2*m+2` otherwise. A separate pure arithmetic theorem shows this family escapes every residue tested by the earlier shallow dyadic tower. Local Lean 4.36.0-rc2 preflight compiled all new proof bodies without `sorryAx` against exact-signature dependency stubs; full original-source recompilation remains outstanding. The source-locus exclusion is an intermediate result and does not establish global Machine C nonhalting.

## Remaining question

Exclude all authentic blank-root stopping parameters across both infinite families or exhibit an original-source halting witness. The completeness of the algebraic stopping locus itself gives no root-reachability result. See the [full log](FULL_RESEARCH_LOG.md) for exact parameter families, proof source files, mathematical derivations, checks and counterexamples.

## 2026-11-07: M192 coverage audit and residual families

The earlier unconditional claim that the M192 backward invariant excludes every
c=0 state with k≥8 was withdrawn. In Core192All, the low predicate requires
the finite residue predicate lowCore(x,w) as a conjunct, in addition to the
disjunction containing 8≤k. A lower bound on k alone cannot establish low.

The corrected M192GeneralBound.lean now proves:
- a conditional source exclusion when the actual lowCore residue condition holds;
- k≥8 for every positive-index first stopping-family parameter;
- k≥10 for every nonexceptional second stopping-family parameter.

The missing residue condition is substantive. For the first family, m=1 gives
(a,k)=(1,25), with 25+3+4=32=2^5, and lowCore(1,25) is false. For the
second family, (j,m,k)=(0,1,40) gives (a,k)=(3,40), with
40+0+3+5=48=2^4·3, and lowCore(3,40) is false. These examples are not claims
of reachability; they show that the current M192 invariant does not exclude
the entire stopping families.

NoMachineCHalt.lean records the exact nontrivial residual stopping
families after the two small feeder exclusions. The corrected
`Agent41M192.lowCore` namespace bridge now compiles in the original-source
workflow; CFeeder's `source_no_3_7` also compiles without `sorryAx`.
The next U5 quotient integration compiled its q=0 parent exclusion but
failed in `q0_w1_z1_target_unreachable` at a deep `decide` reduction and
an unavailable `by_contra` tactic. That proof now sets the M16 quotient
recursion/heartbeat options and uses core `by_cases` plus an explicit
divisibility argument; this repair still needs focused compilation.
None of these reductions proves that Machine C is nonhalting. The remaining
reachability questions are open.




## 2026-11-26: U5 q=0, w=7 source-parent fan (intermediate)

[Detailed derivation and exact parameter formulas](U5Q0W7SourceParentAnalysis.md).

### Parent fan

Write \(z=2+4u\), so the q=0 target is

\[
P(u)=(17928+28896u,\;17719+28560u).
\]

Let \(W=2228+3591u\) and \(X_2=53366+86016u\). The original-source parent fan in
[U5Q0W7ParentFan.lean](U5Q0W7ParentFan.lean) proves that any blank-reachable
\(P(u)\) has a parent \((a,k)\) and an even depth \(n\) satisfying

\[
2^{n+1}(a+3)=16W,\qquad 2k+a+7+3n=X_2.
\]

When \(W\) is odd, the depth is at most two, hence \(n=0\) or \(n=2\).
The depth-zero parent is excluded by the existing source-certified q=0
parent obstruction. The only remaining parent is the q=1 state

\[
Q(u)=(2W-3,\;24450+39417u).
\]

### q=1 parent exclusions

Three disjoint infinite parameter slices of \(Q(u)\) are now excluded:

1. **\(u=59+80t\)** — the existing parent-fan theorem
   w7_z2_q1_parent_unreachable_u59mod80 forces an odd/odd parent and
   reaches the odd-right sum-one blank-image obstruction. This is the
   previously identified \(w\equiv439\pmod{512}\) sublift.

2. **\(u=7+32t\)** — [U5Q0W7U7Mod32.lean](U5Q0W7U7Mod32.lean)
   applies the odd/odd low-valuation parent, then the even/even unique
   parent. The final state is
   \[
   (416500+1749048t,\;119477+501732t),
   \]
   whose right coordinate is odd and whose coordinate sum is \(1\pmod4\).
   The source-certified odd-right sum-one invariant excludes it.

3. **\(u=35+64t\)** — [U5Q0W7U3Mod64.lean](U5Q0W7U3Mod64.lean)
   applies the odd/odd low-valuation parent, then the odd-seven unique
   parent. The final state is
   \[
   (973457+1749048t,\;1045221+1877988t),
   \]
   whose right coordinate is odd and whose coordinate sum is \(2\pmod4\).
   The source-certified odd-right sum-two invariant excludes it.


4. **\(u=23+512s\)** — [U5Q0W7U23Mod512.lean](U5Q0W7U23Mod512.lean)
   applies four exact parent steps: odd/odd low-value, even/even unique,
   odd-seven, then odd/odd low-value. The final state is
   \[
   (715594+15511608s,\;658051+14264292s),
   \]
   whose right coordinate is odd and whose coordinate sum is \(1\pmod4\).
   The source-certified odd-right sum-one invariant excludes it.
For all four slices, \(z=2+4u\equiv14\pmod{16}\). The necessary root
relation \(5z-7s\equiv12\pmod{16}\), with \(w=7+8s\), therefore forces
\(s\equiv6\pmod{16}\) and \(w\equiv55\pmod{128}\). The additional
root condition \(z\equiv3\pmod5\) requires \(t\equiv1\pmod5\) in the
\(u=7+32t\) and \(u=35+64t\) slices; it holds for every \(t\) in
the \(u=59+80t\) slice, and requires \(s\equiv3\pmod5\) for
\(u=23+512s\). These are necessary-residue-compatible
subfamilies, not a classification of the full \(w=7\) progression.

### Exact-source verification

The focused workflow target w7-q0-parent-fan in
[agent3-u5-m32-w485-highstop.yml](../../.github/workflows/agent3-u5-m32-w485-highstop.yml)
passed in run [#20](https://github.com/FlareZ123/bb6/actions/runs/45796426913).
Lean 4.36.0-rc2 compiled 48 project modules from the three roots
U5Q0W7ParentFan, U5Q0W7U3Mod64, and U5Q0W7U7Mod32. The workflow's
axiom guard passed: the printed dependencies of the new declarations are
only propext, Classical.choice, and Quot.sound (with some existing
source invariants using the subset propext, Quot.sound); no
sorryAx or native_decide dependency occurs in this closure.

The four older \(z=4u\) draft lifts below were deliberately excluded from
this focused closure. The earlier broad batch failed in those independent
files at their existing change proofs; they remain intermediate drafts
and are not covered by run #20.

### Remaining scope

This does **not** close the full \(w=7\) progression or prove Machine C
nonhalting. Other q=1 parameter residues, even-\(W\) cases with deeper
parent fans, and the remaining \(z\equiv2\pmod4\) branches remain open.
The \(z\equiv0\pmod4\) four-lift chain below is still an uncompiled
intermediate investigation.

### \(z=4u\) lead (uncompiled intermediate)

For odd \(u\), the \(z=4u\) q=0 target has a unique \(Q_z\) parent;
that parent has a unique odd/odd low-value parent
\(R_u=(3450+28686u,\;3447+28665u)\), an even/even state with sum
\(6897+57351u\) divisible by three. Four sublifts have been algebraically
reduced to source-forbidden terminal states, but their Lean modules have
not passed exact-source compilation:

- \(u=3+16v\) (\(z=12+64v\)):
  U5Q0W7Z4U3Mod16.lean, two even-right inverses;
- \(u=15+64t\) (\(z=60+256t\)):
  U5Q0W7Z4R3Mod16.lean, four even-right inverses;
- \(u=23+128q\) (\(z=92+512q\)):
  U5Q0W7R5Mod32.lean, three even-right inverses then an even/odd sum-three inverse;
- \(u=471+512s\) (\(z=1884+2048s\)):
  U5Q0W7R21Mod128.lean, three even-right inverses, an even/odd sum-three inverse,
  then an odd/odd low-value inverse.

The first two and fourth are claimed to terminate at odd-right sum-one
states; the third at odd/odd sum-two. Treat these only as algebraic
intermediate claims until each module has its own exact-source closure and
axiom audit. For \(u\equiv2\pmod4\), the exact three-way even/even parent
fan is mapped: its zero-left branch is impossible because
\(S=99642+143367v\) is divisible by three, while the direct parent and
even-\(a\) bounce remain unresolved. Other odd-\(u\) lifts and all
even-\(u\)/high-depth branches remain open; see
[U5Q0W7SourceParentAnalysis.md](U5Q0W7SourceParentAnalysis.md) and
[the Agent11 parent-fan question](../../communications/agent11/20261119T084000Z_agent15-w7-z4-even-even-parent.md).
