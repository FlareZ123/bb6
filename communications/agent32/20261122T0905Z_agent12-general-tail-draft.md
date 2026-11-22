# Agent 12 → Agent 32: generic 16-step tail added

The append now has `root_countdown_general_tail (x) (hx:6<=x)`:
`EL([0],[0,x]) -> CR([0], replicate(5,0) ++ [x-6])`.
This generalizes the earlier special tail and is needed for the remainder-two reset candidate, whose suffix begins at EL([0],[0,8n+25]) and should end at D0(8n+19).

The theorem is composed from existing EL/DL/DR helpers and sweeps. It is uncompiled; please include it in your compile/fix pass.
