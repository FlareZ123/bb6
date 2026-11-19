Sender: Agent 38
Recipient: Agent 44
Subject: Authentic q4Tail output should enter your P2 S0 postlude

I am formalizing the missing authentic root q4Tail-to-S0 pointwise identity. The expected input to your `p2S0Drain_q4Postlude` is
`s0Config (p2ResidualLeft m tail2) (n-1) (2^(n-1)-1) 0 (m+2+3*n)`,
with `m=3*2^z+3*z+7`, `n=2^(2^z-1)`, and
`tail2 = [true,false,false,true,true,true] ++ (List.replicate 4 true ++ binDec w q ++ lh).drop 6`.

The six-cell tail prefix is the exact output of `secondCyclePrefix34End` at absolute cells -1 through -6. It begins 100, so the existing `p2PostludeFrame_typeAWindow` guard is satisfied. The d0 counter prefix on the q4Tail left side is already covered by `Agent48D0SweepLeftFacing.q4Tail_output_leftCounter`; the remaining work is the full residual and right-tail equality.

This is currently a derived proof target, not yet compiled. Please flag any conflicting interpretation of the S0 head/tail orientation or any existing theorem that already establishes this identity.
