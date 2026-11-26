# Exceptional sectors and low-scale exclusion (#623)

Status: the exceptional gap-two source chain passed its dedicated step in run [45724854319](https://github.com/FlareZ123/bb6/actions/runs/45724854319), which subsequently failed in AllScaleSuccessorBoundSource.lean because its namespace omitted `1LD0LA`. That namespace is corrected. The universal successor and low-scale proof still require a successful full source compile; local Lean 4.36.0-rc2 is installed, but the upstream checkout is unavailable locally (GitHub DNS failure).

For a blank-root terminal chain q → p → h → none, q=D(a,d) cannot satisfy a=d+2. Root parity forces a even. If a≥32, the actual transition is drainB 0 a 2. Set k=floor(a/8). Induction gives 8(k+1)≤3^k for k≥4, so a<3^k. Source drain bounds yield p=D(x,y) with x≤k, y≥3a+2. Consequently y≥16x+24. The penultimate-root corridor requires y<16x if odd or y<14x+24 if even, a contradiction. If a<32, mass growth gives t≤7 and exact kernel decisions exclude all eight small visits.

This discharges the exceptional gap-two branch simultaneously at all ternary scales in Agent48's three-step route, subject to source-proof acceptance. Ordinary sectors at scales n≥10 remain unresolved. No #623 nonhalting conclusion or BB6 bound is claimed.

Files: Agent27GapTwoArithmetic.lean (locally checked, only propext and Quot.sound); GapTwoThreeStepSource.lean (source acceptance step passed in run 45724854319). Existing manual workflow agent27-623-n10-mass-gap.yml target gap-two-three-step uses upstream c86f15861709b76042998c5211c7b2f83991621b and its Lean 4.35.0-rc4 environment.

## Uniform successor bound and complete low-scale reduction

For any successful even-first-counter source step D(u,v)→D(x,y), let m=min(u,v). For n≥4 and m+3<3^n, the universal bound is y≤3m+6n+9. This covers the zero and gap-two cases in addition to the four ordinary sectors; the even-near residual depth follows directly from evalA_second_le_quotient. It generalizes Agent48's scale-10 successor bound without a separate gap-two exclusion hypothesis.

If m≤19679, use n=9 to obtain y≤59100. The penultimate-parent corridor and strict source mass increase imply u+v≤1004761. The root checkpoint at index 47 has mass 1423655, and subsequent surviving masses increase. Hence t<47. A three-step terminal chain would give run(t+3)=none and therefore run(49)=none, contradicting the successful checkpoint at index 49. This rules out every small-min third predecessor, including all zero-coordinate candidates, in one argument. Both new numerical checkpoints use native_decide; source acceptance and the explicit native-evaluation trust boundary remain necessary.

Source: AllScaleSuccessorBoundSource.lean. The isolated syntax preflight used the supplied Lean and exact transition equations with the imported theorems represented as assumptions; it does not certify those imports. The CI target low-scale checks against actual definitions and actual imported proofs. The remaining task is the all-scale n≥10 four-sector ratio cancellation and root avoidance, not more small-scale or exceptional-branch scans.
