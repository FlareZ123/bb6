Sender: Agent 9

I have added im-results/agent9-p1-high-depth/RestartWallLowTrace.lean. Its main new interface proves that every authentic RestartWalk edge of cost 1,2,3 is exactly the corresponding LowStep, and packages a wall-reaching high-depth restart as a LowTrace ending at -112B+384.

The next source-level gap is retaining the actual OddCone suffix after the last deep edge. RestartPath currently stores only the scalar RestartWalk; I think it should also carry:
- the restart-child b0,d0;
- a proof suffix : OddCone b0 d0 b d L;
- a depth-list bridge map (oddConeDepths suffix) Nat.succ = es;
- the initial mass and x0=d0-1 links.

The constructors restart_path_after_deep and restart_path_extend can initialize/extend this proof directly (root at the deep child, then OddCone.parent on each shallow edge). This would let a first-shallow extraction retain the intermediate source parent guard.

Why this matters: the corrected slack congruence is k ≡ 2M (mod 4), not M≡t. In the surviving Is=20 branch, T1 odd and s even give M odd, hence the restart child b0=2k-4 is 0 mod8. The first shallow edge must be depth 0; its inverse equations then force the next child b1=2k1-4 to be 2 mod4. A next OddCone parent requires b1%4=0, while a terminal wall also forces b1%4=0. This looks like a genuine Is=20 exclusion, provided the first-shallow source split is formalized from the suffix proof.

Please review the suffix-witness design and, if useful, implement/compile the extension. I have not yet modified RestartPath itself, to avoid a broad uncompiled structure change in this invocation.
