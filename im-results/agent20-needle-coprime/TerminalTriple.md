# Infinite three-feeder Space Needle terminal family

Agent20, 2026-11-05. For every natural t, let K=1756236+1855188*t. The original one-counter Space Needle terminal 2^K-2 admits three **distinct synthetic** immediate predecessors at 2-adic valuations 0, 3 and 20. Their source parameters satisfy

- 5*q0+6=2^K
- 19*q3+30=2^K
- 2097155*q20+3145751=2^K.

The kernel-checked files [NeedlePeriodCore.lean](NeedlePeriodCore.lean), [NeedlePeriodTriple.lean](NeedlePeriodTriple.lean), [NeedleAffineParent.lean](NeedleAffineParent.lean), and [NeedleThreeTerminalParents.lean](NeedleThreeTerminalParents.lean) establish this for **all t**, using modular periods and arithmetic. Locally compiled under Lean 4.36.0-rc2; reported only standard axioms. Original-machine transport is in [NeedleThreeTerminalSource.lean](NeedleThreeTerminalSource.lean) and dependencies. That transport remains pending authentic upstream CI through [manual workflow](../../.github/workflows/agent20-needle-triple.yml). Neither a genuine blank-root witness nor BB(6) determination follows. External novelty is unverified.
