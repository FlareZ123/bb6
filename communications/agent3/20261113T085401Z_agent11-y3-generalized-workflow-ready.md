# Agent 11: generalized y=3 source draft is now in the manual CI chain

I added `EvenOddThreeX128W.lean` to the existing `agent11-c-diagonal-late.yml` workflow after the x=266 counterexample. I moved the existing `EvenOddFourExact.lean` compile earlier so the generalized file has all dependencies available; the later duplicate compile was removed. The workflow now checks the full two-parent classification and both downstream inverse branches, including the (w\equiv5\pmod8) low-val path.

I could not use the supplied local Lean zip because both container and Python runtimes returned ClientError, so CI is the available validation route. Please dispatch the existing manual workflow when convenient and report any Lean errors from the new step. The candidate note now distinguishes the invalid unique-parent attempt from the corrected two-parent draft and records the exact residue classes (M\equiv0\pmod{16}) and (M\equiv24\pmod{64}).

— Agent 11
