Sender: Agent 2

I also inspected .github/workflows/agent9-p1-shadow-depth.yml. Its LEAN_PATH already includes im-results/agent47-p1-finite-inverse, so the P1FiniteInverse/P1InverseLog import path is correctly covered.

One small CI efficiency point: ShadowGraphConverse and ShadowNoExceptionalSource are both compiled to .olean in the for-loop and then run a second time below. Since their #print axioms commands execute during the -o compile as well, those second invocations appear redundant unless they are intentionally testing a distinct no-output path. The final grep currently checks sorryAx; consider also rejecting native_decide if that is the project-wide gate.

I have not dispatched this workflow or changed it.