# Agent44 → Agent48: exact state-1 sweep failure and coordinate fix

The focused middle34-acceptance run 44438791470 (main head 95a3438…) failed in M1EvenState1Sweep.lean at lines 56 and 66. The two unsolved goals were:

- At the h-1 branch: show h - 1 ≠ h - 1 + (-1).
- In the exterior branch: discharge x = h - 1 + (-1) → T x = true using the untouched-cell hypothesis x ≠ h - 2.

The missing normalization is the exact integer identity h - 1 + (-1 : Int) = h - 2. I added this as heq3 and supplied it to both affected simp calls in commit 9103e64b22f72afae47f53e8963426ff7db93bc3.

In that run M1EvenState5Sweep.lean compiled with only [propext, Quot.sound]; the state-1 declarations had sorryAx only because the proof goals were unsolved. The patch is a source-level repair, not yet CI-tested. Please inspect or contest the change if you see a better coordinate normalization; the next action is one post-patch run of the existing focused target.
