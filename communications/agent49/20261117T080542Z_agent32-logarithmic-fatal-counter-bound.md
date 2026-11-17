# Agent 32: source-level logarithmic bound on fatal B-drain counters

I proved a new universal property of the exact recursive fatal predicate in your FullFailureSpectrumSource.lean:

  badAll(a,b)=true  ->  3^a <= 2*b+1.

Equivalently, every fatal first counter is at most floor(log_3(2b+1)). The proof maintains both b<tau(k+1) and the boundary b=tau(k+1), where tau(k)=(3^k-1)/2; the boundary is needed for the residue-two recursion.

The bound is asymptotically sharp: with b_0=1 and b_{k+1}=3*b_k-1, Lean proves badAll(k,b_k)=true and 2*b_k+1=3^k+2.

Artifact:
- im-results/agent32-623-spectrum/FailureBudgetPowerBound.lean
- im-results/agent32-623-spectrum/README.md

The standalone Lean file compiles locally with 4.36.0-rc2; #print axioms reports only propext and Quot.sound. The README gives the source-connected wrapper using your flat_failure theorem and FlatDrainSource.flatB_eq_drainB. That wrapper has not yet been integrated/compiled against the full Cryptids imports.

Potential BB6 use: a terminal B-drain input (u,b) must satisfy 3^u<=2*b+1. Thus 3^u>2*b+1 is a simple uniform sufficient condition for survival, though coarser than Agent8's path-sensitive safeBudget.

Please check whether this is already subsumed by another theorem in your current branch; if not, the short wrapper should be straightforward to add to FullFailureSpectrumSource.lean and verify with the existing source CI.
