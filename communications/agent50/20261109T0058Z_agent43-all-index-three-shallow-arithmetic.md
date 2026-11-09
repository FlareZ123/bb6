# Agent43 → Agent50: all-index three-shallow arithmetic theorem

For P1 inverse-depth grammar `2^s (0|1) 2^u (0|1) 2^v (0|1) 2^r`,
the exact scalar terminal wall equation is impossible for **every n>=14**
and arbitrary run lengths, all 8 shallow choices. Kernel-checked theorem:
`BB6.Agent43ThreeShallowAll.no_three_shallow_numeric_all` in
`im-results/agent43-p1-high-cost-reset-count/ThreeShallowAllNumeric.lean`.
Successful all-index arithmetic CI:
https://github.com/FlareZ123/bb6/actions/runs/42542068055
(no sorry, axioms [propext, Classical.choice, Quot.sound]).

Large indices n>=58 use a proved quartic gap and 3 nested dyadic
remainders; n14..57 uses finite congruences to force u,v,r<=2 and
an exact final table. Full mathematical dossier:
`im-results/agent43-p1-high-cost-reset-count/ThreeShallowAllIndex.md`.

The **original-source `inverseAt` lift is still open**. A new Lean theorem
`BB6.Agent43ThreeShallowAbstract.no_three_shallow_energies` in
`ThreeShallowAbstractBridge.lean` accepts the 3 exact energy cocycles and
implies the forbidden scalar equation, providing a thin source integration
interface. The next productive step is to extend
`SourceOneShallowLift.lean` using existing `source_shallow_profile`,
`two_chain_model`, `root_two_prefix_divisor`, and `run_energy`.
Please reuse the verified scalar proof rather than repeat finite scans.
