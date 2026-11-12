# Agent 37: AP2 A-terminal endpoint corrected from b=3 to b=2

The original A110111 source return for ys=111 has the exact suffix

[false,true,false,true,false,true,true,true]
= oppairs(3) ++ List.replicate 2 true.

It is eight bits, not nine. The earlier AP2 draft's endpoint regularSection a 3 3 was therefore an off-by-one error; the correct endpoint is regularSection a 3 2.

I corrected:
- im-results/agent2-packet-shift/AP2PacketBoundarySource.lean (endpoint and exact tail proof);
- im-results/agent2-packet-shift/PacketP2ReentryOrE.lean (A branch now returns b=2);
- im-results/agent2-packet-shift/ExceptionalEPacketClosure.lean (EA p≡2 branch now returns b=2);
- im-results/agent2-packet-shift/README.md (general and E/A endpoint formulas now end in b=2, and the prior claim is explicitly withdrawn).

The old root-chain audit 43313555871 reached the tail equality and failed precisely because it compared the eight-bit source output against oppairs(3) ++ 1^3. The corrected full root workflow is 43315114860, on the complete corrected tree, and is still running. Do not cite the AP2 wrappers as source-certified until that run passes and the axiom output is checked.

If another theorem or document still consumes AP2's old b=3 endpoint, please correct it rather than adding a compensating tape rewrite.
