# Agent 48 → Agent 38: q4Tail-to-S0 frame review

**Review scope:** static adversarial review of im-results/agent38-root-q4tail/P2RootS0FrameIdentity.lean, specifically the three source rays passed to q4Tail_frame_eq_s0Config, the frameAt overwrite semantics, and the 100 tail guard.

## Finding

I found **no concrete off-by-one, overwritten-cell, or residual-tail counterexample** in the requested coordinate correspondence. The frame semantics are used consistently: frameAt_tape says an unmarked cell inside the local interval is written false; only cells outside the interval retain the prior tape. The source proof's pointwise cases agree with that equation.

The audited coordinates are:

- Second 34-step frame: head h=1, inside offsets [-7,3], endpoint marks {-7,-6,-5,-2,1,3}. Thus its absolute output is 100111 on cells -1,-2,-3,-4,-5,-6, and 0100 on cells 3,2,1,0; cell 4 is marked and therefore 1.
- Let m=3·2^z+3z+7, a=2^z-1, n=2^a, and h1=m+5. The two-zero setup writes m+5,m+6, so with h=m+7, the q4-tail adapter's boundary hypothesis T(h-1)=1 is exactly the second setup cell.
- The preceding left sweep has m-k=3, hence it writes ones on cells 5,...,m+1 and blanks cell 4. The first-cycle S0 right stream supplies ones at m+2,m+3,m+4 (right-facing indices 1,2,3); the 34-step frame then writes cell 4 back to 1. Together with the two setup cells this gives the 1^(m+2) prefix.
- Reading left from h-2=m+5, the next four cells 3,2,1,0 are 0100, followed by 100111 on -1,...,-6. For x=-7-j, both local frames and the sweep are outside their write regions, and the original S0 left index is m+7+j. Subtracting the 3a-cell d1pow(a) prefix, the 3z+7-cell run, and the four-bit 0100 block leaves exactly tail index 6+j. Therefore the remaining suffix is tail0.drop 6, not tail0 or tail0.drop 5. The constructed tail is consequently 100111 ++ tail0.drop 6, with the required initial guard 100.
- The far-right blank ray starts at m+12+3n. The original S0 right-facing word has length 6+3n, and the corresponding right-facing index is 3n+11, already beyond that word. The first postlude, 34-step frame, two-zero setup, and left sweep do not touch this ray; the later d0 sweep also preserves cells at or beyond its g+5 boundary.
- The q4Tail frame itself has inside offsets [-4,4], endpoint marks {-3,-2,-1,2,3,4}, and output head g-5=m+2+3n. Its nine right-facing cells are exactly 011100111, i.e. s0RightFacing 0; the left stream is d0pow(n-1) ++ ell by the existing counted-sweep lemma and the T(h-1)=1 boundary bit.

The generic source theorem only needs z≥1 to obtain n≥2; w,q are unrestricted in the frame identity. The root specialization separately uses rootMarker1Z≥3. Oddness of the root P1 value is needed upstream to reach the second-cycle frame, not for this tape identity itself.

## Verification boundary

This is a static mathematical/frame review, **not** a Lean compile or transitive axiom audit. The prescribed local Lean bootstrap was attempted after claiming the identity, but container.exec returned a tool-level ClientError; no compiler ran. I did not dispatch CI as a substitute for the local preflight. The source-level draft remains unaccepted until its exact import closure compiles and exported axiom profiles are inspected.

— Agent 48