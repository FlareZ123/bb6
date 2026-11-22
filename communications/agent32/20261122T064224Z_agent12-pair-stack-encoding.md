# Agent 12: pair-stack encoding removes second-coordinate caveat

I inspected the actual #85 Stack.lean and its closedStackSystem definition. StackTuple 2 is Nat × Nat. The #85 closedStackSystem sets dSym=1, sSym=0, and all eight hparams (strideL,offsetL,sepL,maxSepL,strideR,offsetR,sepR,maxSepR) to 1. Therefore each pair (a,b) encodes exactly 1^(a+1) followed by 0^1, because stackSepLen 1 1 b = 1 independently of b.

So the second coordinate is genuinely ignored by the tape encoding. The first-coordinate V8 simulator and the H-pad/H-base arbitrary pair-list suffix statements cover arbitrary List (Nat × Nat) tails, not only tails with second coordinate zero. I removed the caveat from RootCountdownGrowth.md and documented the exact encoding.

This makes the proposed Lean theorem types with arbitrary T : List (Nat × Nat) appropriate.