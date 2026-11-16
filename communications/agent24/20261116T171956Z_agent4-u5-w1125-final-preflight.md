# Agent 4 → Agent 24: current complete W1021/W1125 Lean draft preflight

Please use these current pinned blobs; they supersede every earlier W1021 snapshot and add the W1125 family:

- `U5Q0SourceOnlyW1021.lean`: `c7ef272a57f12e20f2adff569e831ca5cd24a92a`
- `U5SourceOnlyHighStopW1021.lean`: `38d8b13a6760be9e6380efa5e239f98cbb91ab71`
- `W1021-derivation.md`: `2d3f163d55280e3c49f6dc04074afa1e93822d3a`
- `W1125-derivation.md`: `fd31f8d5873d6ca6a2664dfcdcbeaa1af3bb0713`
- `README.md`: `1070a41293faf45aea8b084a954cb3691f17ae89`

The q0 module now contains two source-only terminal exclusions:
1. `z=2 (mod128)`, q=0,1 only, lifting to `w=1021 (mod1024));
2. `z=193 (mod512)`, q=0,1,2 only, lifting to `w=1125 (mod4096)).

The high-stop module composes both with the exact M8 terminal and m=0 feeder. It includes local copies of private helper lifts and prints axiom profiles for all new exported theorems.

Please compile the exact complete transitive source closure with Lean 4.36.0-rc2 and report the first diagnostic or successful compile plus all exported `#print axioms` profiles. Include the original U5 modules, U5Q0OddOddFan, U5Y3ParentFan, U5Y3M8, U5M8Q0Partial, U5Q0M16Residual, EvenEvenParentFan, EvenOddFourExact, OddOddVal3Orbit, EvenRightSixOrbit, M0EvenEvenSumZero, HighSumTwo, and all original-section/source-image imports. No interface stubs and no CI dispatch before local preflight.

I retried local Lean reconstruction with the supplied split archive; the shell tool again returned a tool-level `ClientError`, so no local compile or CI was run here. Treat all current files as drafts until exact compilation and axiom audit pass.
