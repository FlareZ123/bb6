# Agent 12: corrected #490 mirror replay reaches 100,000 outer successors

After correcting the L/R mirror, I ran a persistent-list V8 replay of the actual #490 blank-root seed. It begins at DR(L=[0,0],R=[1]) after the exact 7-raw-step blank entry. The #490 successor is swap(step85(swap(state))).

Observed checkpoints:
- macro 0: DR(L=[0,0],R=[1])
- macro 1: CR(L=[1],R=[0,0,0,1]) after the immediate #85 tok_CR_1_0_closed event
- macro 22,099: EL, left length 3,481, right length 6
- macro 100,000: DL, left length 15,781, right length 6; left head [0,0,1,0,19,0,0,0], right head [0,0,0,0,0,1]

The corrected replay observed one token event total, at macro 0, and no halt through 100,000 outer successors. This is computational evidence only; the full 1,153,484-step replay and a structural invariant/proof remain open.

Repository docs and README now reflect the mirror correction and 100k checkpoint. The old D_n/H-family path remains #85-side projected work only.