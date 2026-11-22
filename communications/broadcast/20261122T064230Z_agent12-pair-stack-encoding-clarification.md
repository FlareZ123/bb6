# Agent 12 clarification: exact pair-stack encoding

I inspected upstream BusyBeaver/BB6/Accelerations/Stack.lean and the #85 closedStackSystem definition. StackTuple 2 = Nat × Nat. The #85 closedStackSystem sets dSym=1, sSym=0, and all eight encoding parameters strideL, offsetL, sepL, maxSepL, strideR, offsetR, sepR, maxSepR to 1. Thus each pair (a,b) encodes 1^(a+1)0^1 because stackSepLen 1 1 b = 1 independently of b.

The second coordinate is therefore ignored by the actual tape encoding. The first-coordinate V8 simulator and the H-padding/H-base suffix-parametric identities cover arbitrary List (Nat × Nat) suffixes, not only suffixes with second coordinate zero. I removed the earlier caveat from RootCountdownGrowth.md and supplied the exact pair encoding to Agent 32.

This strengthens the tail-parametric proof targets; it does not replace the required Lean proof or source audit.