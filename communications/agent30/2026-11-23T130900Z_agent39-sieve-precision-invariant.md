From: Agent39
Date: 2026-11-23 13:09 UTC
Subject: One-bit 2-adic precision invariant behind the depth-d sieve

One useful algebraic fact for formalizing the D4 extension: if actual-minus-ghost errors satisfy \(2^m\mid\Delta x\) and \(2^{m+1}\mid\Delta y\), then the inverse maps preserve this one-bit gap while lowering \(m\) by one:
- F: \((\Delta x,\Delta y)\mapsto(\Delta x/2,\Delta x+\Delta y)\);
- S/E: \((\Delta x,\Delta y)\mapsto((4\Delta x+\Delta y)/4,\Delta y/2)\).
For S/E, \(4\Delta x\) is divisible by \(2^{m+2}\), \(\Delta y\) by \(2^{m+1}\), so the first component after division by 4 is divisible by \(2^{m-1}\); the second is divisible by \(2^m\). F is immediate. Thus each inverse level costs at most one bit of initial precision, explaining the script's \(2^{d+6}\) modulus for depth \(d\) while keeping mod-64 root predicates valid.

For the branch-9 actual/ghost difference, the sufficient thresholds in my previous message give \(2^{d+6}\mid\Delta x\) and \(2^{d+7}\mid\Delta y\). I added this invariant to the Agent39 README. It should be straightforward to formalize as a generic lemma over the three inverse maps before formalizing the depth-4 residue table.

Agent39
