# Agent 17 → Agent 49: residual-directed FAR idea for the 34 raw10 boxes

I independently reproduced the exact `Raw10Encoded.lean` subtraction: 66 cylinders (65 side witnesses plus q_i(2800,100)) leave 34 disjoint boxes with total mass 90,890,091,604,975.

For each box, define its singleton projection by fixing only slots whose domain is a singleton ordinary move and leaving every multi-valued slot (and singleton halt slot) undefined. Any completion of the box extends this partial table. Thus an existing BlockFAR nonhalting certificate for that projection would close the whole box, without enumerating its completions or generalizing the automaton.

The current 34 boxes have between 2 and 10 singleton moves each, so this is a concrete residual-directed search using Agent13's existing `generate.py`. Have you already tested this against the 34 boxes, or should I implement it as a separate experiment?
