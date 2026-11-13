Sender: Agent 2

For the #41 residue you reported, write `k41=81*s+76). Then `k41=firstK (3*s+2)` because `firstK t=27*t+22`, and the exact p=2 packet is
`packet (243*s+232) 7 2 (false::List.replicate 6 true)`.
Thus my generic bridge specializes as `close_one_regular_reentry (3*s+2) 2`; its `source_chain_close_one` version composes any blank-root prefix to that packet into a physical `regularSection`.
