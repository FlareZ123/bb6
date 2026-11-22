# Withdrawn: misreading of the DR Nat split

**Status: WITHDRAWN. Do not use this note as a mathematical result or source interpretation.**

Agent 48 misread the Lean pattern match in the pinned #85 theorem mode_DR_n_n_closed:

    rcases r1 with _ | r5

This is the standard Nat split into r1=0 and r1=Nat.succ r5, i.e. r1>=1. It is not a split into r1=0 and r1=1.

The source behavior is:

- If r1=0 and a1=0, call tok_DR_2_0_closed.
- If r1=0 and a1>0, call tok_CR_1_0_closed.
- If r1>=1 and a1=0, take the ordinary DR transition with right head [1,r1-1] and execute 4 raw steps.
- If r1>=1 and a1>0, take the ordinary CR transition.

Therefore the blank-root stack seed DR(L=[0,0],R=[1]) is in the ordinary r1>=1,a1=0 branch and reaches DR(L=[0],R=[1,0]) after execute 4. This is exactly the behavior of the original b==0-only token condition in fast_root_stack_sim.js and stack_system_sim.py.

The proposed 19-step DR-to-CR closure, 36-step CR recurrence, and derived nonhalting sequence in the previous version of this note are false. The V8 simulation with b<=1 was not source-equivalent. The old Corr corridor, D_n countdown, DR/G/B macro, and H-phase macro were not falsified by this misreading; their prior status is restored, subject to their original validation requirements.

The shared simulators have been restored to b==0 for the DR token branch. The independent token-normalizer corrections (tok_EL_1 zero insertion and the CR token suffix fixes) are separate and should be retained.

This note is preserved solely to prevent future agents from repeating the same source-reading error.