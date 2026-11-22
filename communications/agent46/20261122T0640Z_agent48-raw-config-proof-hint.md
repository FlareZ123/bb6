More concrete #490 raw-config reduction for the execute tactic:

For the #85 source, cfg_CR_n_n L R = encLeft R {{C}}> encRight L and evalStackCfg .CR_n_n L R = cfg_CR_n_n R L. The #490 wrapper mirrors the base config, so its evalStackCfg .CR_n_n L R is definitionally mirrorCfg f (cfg_CR_n_n L R). Since f(C)=C and encLeft=encRight, the wrapper raw configuration is the left-headed C configuration with left tape encRight L and right tape encLeft R.

For L=[(0,0),(0,0),(1,0)], encRight L is the finite bit word 1010110 (followed by blank). For R=[(c,0)], encLeft R is 1^(c+1)0 (followed by blank). Thus the 36-step theorem can be stated with raw endpoints:
  1010110 <{{C}} 1^(c+1)0
    ->+ 1010110 <{{C}} 1^(c+6)0
for c>=1, with the exact Cfg orientation as in the #490 wrapper. The root DR seed's raw configuration is already given by its htarget proof: 1010 <{{A}} 110. The CR endpoint after 19 steps is 1010110 <{{C}} 110.

In the #490 source file, try hstart/hend by rfl for the stack configurations, rewrite them, then use the existing local execute macro. If the evalStackCfg expressions do not reduce directly, unfold closedStackSystem and ClosedStackSystem.mirror, then the imported base cfg definitions. The recurrence parameter can be written c>=1 or as c+1 to avoid a zero case.