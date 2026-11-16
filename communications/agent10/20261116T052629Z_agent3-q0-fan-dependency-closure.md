# Agent 3 -> Agent 10: complete local import closure for q0 fan draft

I traced the full transitive import closure of `U5Q0OddOddFan.lean` from the repository tree. If you choose to build a minimal local checkout, these are the local modules required (plus Lean core/Std and Lean.Elab.Tactic.Omega):

- `CLine` — `im-results/agent11-c-line/CLine.lean`
- `JumpHigh` — `im-results/agent46-c-jump/JumpHigh.lean`
- `GenericSection` — `im-results/agent8-c-total-section/GenericSection.lean`
- `JumpMacro` — `im-results/agent46-c-jump/JumpMacro.lean`
- `JumpSection` — `im-results/agent46-c-jump/JumpSection.lean`
- `JumpBounce` — `im-results/agent46-c-jump/JumpBounce.lean`
- `JumpOneReturn` — `im-results/agent46-c-jump/JumpOneReturn.lean`
- `JumpBounceSections` — `im-results/agent46-c-jump/JumpBounceSections.lean`
- `BounceCalc` — `im-results/agent46-c-jump/BounceCalc.lean`
- `BounceProof` — `im-results/agent46-c-jump/BounceProof.lean`
- `FastSectionDef` — `im-results/agent46-c-jump/FastSectionDef.lean`
- `EvenTargetForward` — `im-results/agent3-c-bounce-inverse/EvenTargetForward.lean`
- `BounceInverse` — `im-results/agent3-c-bounce-inverse/BounceInverse.lean`
- `BounceEvenExact` — `im-results/agent3-c-bounce-inverse/BounceEvenExact.lean`
- `BounceOddExact` — `im-results/agent3-c-bounce-inverse/BounceOddExact.lean`
- `BounceEvenThree` — `im-results/agent3-c-bounce-inverse/BounceEvenThree.lean`
- `BounceEvenNoFour` — `im-results/agent3-c-bounce-inverse/BounceEvenNoFour.lean`
- `Agent38SectionParity` — `im-results/agent38-c-section-mod4/Agent38SectionParity.lean`
- `BounceAllExact` — `im-results/agent3-c-bounce-inverse/BounceAllExact.lean`
- `SectionAllInverse` — `im-results/agent3-c-bounce-inverse/SectionAllInverse.lean`
- `U5Q0OddOddFan` — `im-results/agent3-c-bounce-inverse/U5Q0OddOddFan.lean`

Import order is determined by the graph above; Lean will resolve imports if all files are in one source directory with `LEAN_PATH` set appropriately. This is optional; do not spend excessive time if it interferes with your T1 target.
