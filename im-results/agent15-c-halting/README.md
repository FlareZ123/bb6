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
families after the two small feeder exclusions. Its M192 predicate
references now use the explicit namespace `Agent41M192.lowCore`; the
corrected original-source bridge still requires a focused compile. It does
not prove that Machine C is nonhalting. The remaining reachability
questions are open.



## 2026-11-19: U5 q=0, w=7 source-parent reductions (intermediate)

[Detailed derivation and exact parameter formulas](U5Q0W7SourceParentAnalysis.md).
The q=0 target is
(P_z=(3480+7224z,3439+7140z)), with the residual relation
(5z-7s\equiv12\pmod{16}) for (w=7+8s). The note records:

- a complete original-source parent normal form for the (z=2+4u)
  parity sector, and a derived exclusion for (u\equiv1\pmod4);
  this corresponds to (w\equiv119\pmod{128});
- two uniquely forced odd-z parent chains for (z\equiv5,13\pmod{16}),
  ending in the existing odd-right sum-two blank-image obstruction;
  these correspond to (w\equiv95,31\pmod{128});
- a further source-level q=1/odd-odd low-value chain for
  (w\equiv439\pmod{512}), using the existing odd-right sum-one
  obstruction.

The candidate Lean source is
[U5Q0W7ParentFan.lean](U5Q0W7ParentFan.lean). It remains an
**uncompiled draft** because local shell and Python execution returned
runtime errors in this invocation; no U5-specific CI was dispatched
without local preflight. The (w=439\\pmod{512}) chain is now represented
by `w7_z2_q1_parent_unreachable_u59mod80` and
`w7_q0_target_unreachable_u59mod80`, which formalize the q=1 low-value
parent and the complete q=0 target reduction on that lift. These
declarations still require local compilation and an axiom audit. None
of these slices closes the full w=7 progression or proves Machine C
nonhalting. The remaining odd-z parent cylinders, (z\\equiv0\\pmod4),
and the unresolved (z\\equiv2\\pmod4) high-depth branches remain open.


Additional z=4u lead: P_z has a unique Q_z parent; for odd u, Q_z has a unique odd/odd low-value parent R_u=(3450+28686u,3447+28665u), which is even/even with sum 6897+57351u divisible by 3. Two sublifts are now reduced to odd-right sum-one forbidden states: u=3+16v (z=12+64v) by two even-right inverses in `U5Q0W7Z4U3Mod16.lean`, and u=15+64t (z=60+256t) by four even-right inverses in `U5Q0W7Z4R3Mod16.lean`. Both compositions are uncompiled and unaudited. The other odd-u lifts, including the sum-zero parent forks, and all even-u/high-depth branches remain unresolved; see `communications/agent11/20261119T084000Z_agent15-w7-z4-even-even-parent.md`.
