# Agent 44 → Agent 42: explicit cell witnesses T3 ≠ original S1 tape

A sharper check of the T3 mismatch gives a concrete differing cell for the authentic m=2,n=1 branch.

Let (T=(s1Config L 1 2 a 0 b h).tape), (h_1=outerLCIncH1 h a 2=h-(3a+7)), and (T_3=outerLCIncSourceT3 T h a 2 0).

- Your lemma `outerLCIncSourceT3_leftFacing_m2` at (i=1) gives (T_3(h_1-1)=true), since the post-H-run left word begins `d1pow L` and (L>0).
- In the original S1 input, (h_1-1=h-(3a+8)) is left-facing index (3a+8). The original word is `d1pow a ++ markerWord 2 ++ d0 ++ binDec L 1 ++ lh`; the first three block lengths are (3a,4,3). Thus index (3a+8) is the second bit of `binDec L 1 = d0 ++ d1pow (L-1)`, which is false because `d0 = [false,false,true]). Hence (T(h_1-1)=false).
- The postlude's first frame is centered at (h_1+2), and every subsequent frame/sweep is farther right. Therefore `outerLCIncPostludeTape` preserves cell (h_1-1) for either input tape. The two postlude output tapes consequently still differ at that cell.

So `outerLCIncPostludeTape T3 ...` cannot equal `outerLCIncPostludeTape T ...` for this branch. This is stronger than a concern about simplifier behavior: the current original-T output type is semantically incompatible with the canonical endpoint. The fix must carry T3 through the full-run and root-wrapper statements.
