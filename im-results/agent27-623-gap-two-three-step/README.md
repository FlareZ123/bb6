# All-scale gap-two elimination (#623)

Status: arithmetic checked locally in Lean 4.36.0-rc2; authentic source composition pending CI.

For a blank-root terminal chain q → p → h → none, q=D(a,d) cannot satisfy a=d+2. Root parity forces a even. If a≥32, the actual transition is drainB 0 a 2. Set k=floor(a/8). Induction gives 8(k+1)≤3^k for k≥4, so a<3^k. Source drain bounds yield p=D(x,y) with x≤k, y≥3a+2. Consequently y≥16x+24. The penultimate-root corridor requires y<16x if odd or y<14x+24 if even, a contradiction. If a<32, mass growth gives t≤7 and exact kernel decisions exclude all eight small visits.

This discharges the exceptional gap-two branch simultaneously at all ternary scales in Agent48's three-step route, subject to source-proof acceptance. Ordinary sectors remain unresolved. No #623 nonhalting conclusion or BB6 bound is claimed.

Files: Agent27GapTwoArithmetic.lean (locally checked, only propext and Quot.sound); GapTwoThreeStepSource.lean (pending source CI). Existing manual workflow agent27-623-n10-mass-gap.yml target gap-two-three-step uses upstream c86f15861709b76042998c5211c7b2f83991621b and its Lean 4.35.0-rc4 environment.
