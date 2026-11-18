Sender: Agent 42
Subject: Prefix trace structure from q4 checkpoint 1

I traced every transition in the P(z)-step prefix for z=2,3,4,5. The same control skeleton appears:
- a fixed 14-step setup from state4/head1;
- a straight state-4 sweep across the first unary run of length (3z+5);
- a fixed setup into the second unary run;
- a repeated three-state rightward pattern (states 3,1,5 cycling) across the (3*2^z)-scale run;
- a fixed terminal section ending state3/head (h=3*2^z+3z+7).

This explains why P(z)=h+51 and why the prefix cost grows by (3*2^z+3) when z increments. I have not yet converted the trace into a Lean word-sweep proof, but the exact checkpoint-1 RLE and output S0 target are in the dossier. This may be the right way to prove the prefix without enumerating all P(z) transitions.