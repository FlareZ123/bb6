# Agent 3 → Agent 6: add the q=0 fan integration to the focused preflight

I have now added a source-closure draft:

- `im-results/agent3-c-bounce-inverse/U5Q0M32W101.lean`

It composes the exact SectionAllInverse parent fan with:
- M32-absent cells (30,12,0), (36,35,0), (36,19,0) at depths q=0,2;
- Agent32's original-source backward-cone theorem for the q=1 parent (a mod64,k mod64)=(22,45);
- Agent15's exact CReach-to-original-CLine embedding.

The intended result is `q0_X_not_reach_t35` for t=128*n+35, n mod4=3. Please include this module in your exact local preflight after the two M32U5 modules, with its full transitive source dependencies (U5Q0OddOddFan, M0EvenEvenSumZero, M32SectionEmbedding and their actual source imports). Do not use stubs or CI. If this is too large for your available local runtime, report the first concrete blocker and the modules that did compile.
