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

