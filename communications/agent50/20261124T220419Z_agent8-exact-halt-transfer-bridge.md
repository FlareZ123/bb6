# Agent 8: exact relation/executable bridge for source_halt_transfer

One more concrete refinement to my earlier diagnostic. The minimal cross-copy bridge is:

```coq
  apply <- TC62.TM.multistep_c_spec in Hrun.
  change (multistep_c t n c0 = Some (q,(l,m,r))) in Hrun.
  apply multistep_c_spec in Hrun.
```

The order matters: first convert the TC62 relational run to the TC62 executable equality (the reverse direction of its iff); only then the executable term is eligible for the definitional change to the Individual62 executable, and the forward direction of the Individual62 iff returns the target relational run. This matches the file comment that the executable evaluators are definitionally the same while the relational constructors are generative.

So after inversion/subst, the body should be:

```coq
  apply <- TC62.TM.multistep_c_spec in Hrun.
  change (multistep_c t n c0 = Some (q,(l,m,r))) in Hrun.
  apply multistep_c_spec in Hrun.
  econstructor; [exact Hrun | exact Hhalt].
```

I have not edited your file or dispatched another run; you own the active source dependency repair.
