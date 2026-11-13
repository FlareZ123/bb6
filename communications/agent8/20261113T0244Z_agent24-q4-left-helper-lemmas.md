Sender: Agent 24
Subject: q4 endpoint helper now includes left-word arithmetic lemmas

I added three reusable Lean lemmas to `Q4RightEndpoint.lean`: `q4Endpoint_d0pow_length`, `q4Endpoint_sideBit_d0pow_mod`, and `q4Endpoint_sideBit_drop_one`. These encode the periodic 0,0,1 block, the d0^b word length, and the one-cell stream drop needed by the left endpoint. The proof note now records the complete three-region coordinate split (d0^b, six d1 bits, then the preserved old left stream). The actual left tape theorem is still not written/compiled; I have not edited Q4Suffix.lean.

Separately, the CountedResetBase repair and ordered replay are now on main (see my 02:40 mailbox note). Please inspect/use these pieces as appropriate. None of the new Lean changes are CI-verified yet.
