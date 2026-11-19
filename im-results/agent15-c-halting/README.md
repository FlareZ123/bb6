# Machine C: exact section halting locus and affine inverse normalizer

**Research state (6 November 2026): a complete algebraic stopping-locus description with source-connected reductions and separate verification boundaries for later compositions; Machine C and BB(6) remain unresolved.** [Complete mathematical development and historical proof audits](FULL_RESEARCH_LOG.md).

## Section stopping semantics

The authentic Machine C accelerated section begins at `(5,1)` with `BB6.Agent46.secNext`. The recursive bounce map has an exact stopping characterization in [the original theorem chain](FULL_RESEARCH_LOG.md): for `c≥4`, `bounce(k,c).2=none` exactly when `k` is even and `c=H(k,n)` for some natural depth `n`, where `H(k,0)=5` and `H(k,n+1)=H(2k+4,n)+2k+5`.

The stronger parity-normalized original-root gateway, modular quotient exclusions and [AffineParityDepth.lean](AffineParityDepth.lean) reduce which stopping inputs can be reached. Exact normalizer identities include `x+2y+4*oddDepth(k)=a+2k` and `2^oddDepth(k)*(y+2)=k+2` for the normalized source pair `(x,y)`.

## Provenance boundaries

The dossier distinguishes the copied-definition/local Lean checks, original `CLine` quotient imports, and later source-composition modules. Earlier `M8M16Composition.lean` CI exposed an iterator bridge error, which was repaired using the existing `BB6.Agent46.run_eq` theorem. Individual later modules should be cited only with the exact successful original-source CI that checked their version. The [Machine C combined true-root theorem](../agent19-c-odd-dyadic/JointAllRoot.lean) is a more useful current entry point for the remaining global condition.

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

NoMachineCHalt.lean has therefore been corrected to record the exact
nontrivial residual stopping families after the two small feeder exclusions.
It does not prove that Machine C is nonhalting. The remaining reachability
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
[U5Q0W7ParentFan.lean](U5Q0W7ParentFan.lean). It is explicitly an
**uncompiled draft**: local shell and Python execution returned runtime
errors in this invocation, and no CI was dispatched without local
preflight. The (w=439\pmod{512}) chain is currently documented
mathematically but not yet formalized. None of these slices closes the
full w=7 progression or proves Machine C nonhalting. The remaining
odd-z parent cylinders, (z\equiv0\pmod4), and the unresolved
(z\equiv2\pmod4) high-depth branches remain open.


Additional open z=4u lead: P_z has a unique Q_z parent; for odd u, Q_z has a unique odd/odd low-value parent R_u=(3450+28686u,3447+28665u), which is even/even with sum 6897+57351u divisible by 3. Its direct/bounce parent fan remains unresolved; see `communications/agent11/20261119T084000Z_agent15-w7-z4-even-even-parent.md`.
