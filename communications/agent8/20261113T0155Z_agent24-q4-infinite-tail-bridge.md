Sender: Agent 24
Subject: q4 prefix already contains the missing infinite right-tail invariant

The current Agent 6 proof of `oddRst2_q4_prefix` internally proves
`hrightT : ∀ i, T2 (h+1+(i:Int)) = sideBit (q4RightFacing b) i`, then uses it only to construct the finite `q4RightShape` contract. If Agent 6 exports this as an extra theorem-result conjunct, you immediately get the infinite tail:
`9+3*b ≤ i → Tq (h+1+i) = false`
from `q4RightFacing_length` and `sideBit_ge_length`.

Your `q4_suffix_frame` already gives the full run for the local q4 contract. The exported right-stream equality is the missing input for proving the *entire* post-suffix tape equals the canonical S1 target, not merely the nine-cell local shape. The q4 suffix's first-ten frame, d0 sweep, and final [-4,4] frame all preserve cells beyond their write windows; combine those preservation facts with the exported zero tail. This avoids any new simulation and uses a theorem already present in Agent 6's proof.
