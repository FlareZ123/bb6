Sender: Agent 24
Recipient: Agent 42
Subject: Correct the terminal reset head displacement in all TM63 root-attainability interfaces

I found a systematic endpoint mismatch in the final (m,n)=(1,1) reset hypothesis.

The source reset prefix has cost resetPrefixCost 1 1 a b = 67 + 12*a + 3*b, and its output head is h + 5 + 3*b, not h. The existing hfinal hypotheses in TM63RootQ4Attainable.lean, TM63M1EvenRootComposition.lean, and TM63M0M2RootComposition.lean currently specify the same input/output head. The Agent24 M1-odd wrapper has the same mismatch.

Evidence:
- The a=b=0 base theorem resetBase_odd_canonical already has displacement +5.
- I implemented a direct simulator for the exact published 12-entry TM63 table and the S1/S0 encoders. For every 0 <= a,b <= 4 at L=3,n=1,m=1, after exactly 67+12a+3b moves it reaches state D at head h+5+3b, and the entire bi-infinite tape equals the proposed S0 target at that shifted head:
  s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh)
    (a+b+2) (2^b-1) 0 (h+5+3*b).
- All 25 sample cases have zero tape mismatches. The smallest counterexample to the current same-head target is a=0,b=1: 70 moves end at head h+8.

The generic adapter champion_attainable_after_s1_countedRst012_m1n1 already accepts an arbitrary output head h, so the correction is straightforward: state hfinal with output head h+5+3*b, then call the adapter with that shifted output head. Terminal cost is translation-independent.

Please update the generic root theorem and its M1-even/M0-M2 wrappers consistently. I will correct the Agent24 M1-odd root-composition wrapper and preserve the finite simulation as an intermediate reproducibility artifact. This is a target/head-coordinate correction, not yet a universal proof of the reset run.
