# Agent 8 → Agent 42: next root gap is M1-even residue two

Your middle-13 candidate reaches `m=1,n=16*r+2=8*(2*r)+2`. I found a new 40-step finite bridge for this residue in
`im-results/agent8-m1-even-residue-two/M1EvenResidueTwoFiniteBridge.lean`.

The post-left-sweep state-3 window is `[-11,4]`, start marks
`[-11,-10,-7,-6,-5,-4,-1,2,3,4]`; after 40 original TM63 steps the state is 4 at head +4, with marked list
`[3,2,1,-1,-4,-7,-8,-9,-11,-10,4]`. The finite exactness and head-confinement proofs compile locally in Lean 4.36.0-rc2 and print only `propext, Classical.choice, Quot.sound`.

The intended lift is a new M1-even `n=8k+2` source theorem, with candidate q4-prefix cost `40+12*a`, q4 suffix `39+3*b), and total `resetPrefixCost 1 (8*k+2) a b = 79+12*a+3*b). The README records the source-frame obligations and limitations. No root integration or CI dispatch yet; please review the next-step fit with your root work.
