# Reachable-profile quotient of a two-sided stack certificate

Let S be the finite relation of abstract reachable configurations (q,a,l,r), with left/right stack sets L,R, deterministic partial push functions and inverse-pop edge relations. The checker requires the blank configuration, blank pop edges, a defined machine transition at every member of S, a valid push edge and closure under every pop edge.

Define l~l' iff for every q,a,r, membership (q,a,l,r) in S agrees with (q,a,l',r); define r~r' dually. Project S and the inverse-pop edges to the equivalence classes. For a written bit b, choose any defined representative push in each class, project its destination, and leave unused pushes arbitrary. Use class index 0 for the original blank state.

**Preservation theorem (mathematical proof).** Every class product is saturated: if (q,a,[l],[r]) belongs to the projected relation, every representative pair belongs to S, by applying the left and then right equal-profile identities. Consider a checked transition moving right from a projected member. Choose the original left representative whose defined push supplied the quotient push. For any projected right pop edge, choose its original right source representative and predecessor. Saturation places the chosen left and right representatives together in S. The original closure check supplies both the push-edge membership and the required successor for that original pop edge. Project those two facts. The same proof with left/right exchanged handles moves left. The blank member and blank edges project directly. Defined representative pushes exist whenever a projected configuration requires them because every corresponding original configuration is checked. Thus the projected certificate is valid. Repetition to a fixed point terminates because every nontrivial step strictly decreases at least one finite stack-state count.

This is a constructive preprocessing algorithm, not a new trusted acceptance rule. The original TwoSidedAutomata checker still checks all output. Implementation: minimize_cert.py in this directory. Raw56 E1=1RE examples:
- E0=0LF M760: 9672 -> 204 joint configurations, 597/11 -> 16/9 stack states.
- E0=0RF M108: 7006 -> 214, 192/21 -> 20/6. The original literal certificate OOMed locally; the quotient certificate and complete child bound 10000 subsequently passed the original Lean checker.
- E0=1LF M150: 3436 -> 282.
- E0=0LF M204: 3372 -> 171.
- E0=1LA M546 and E0=1LF M1070: 3138 -> 300 each.

This approach is independent of how the original candidate was discovered (ngram, RLE, periodic-block, lag-XOR, or arbitrary finite stack relation). It can be applied to FastBiDFA witnesses after constructing their reachable configuration relation, provided the resulting inverse-edge certificate is checked by the appropriate soundness theorem. Do not claim that quotienting an ordinary DFA always preserves its language: the invariant here is the joint reachable relation and the dynamic pop-edge closure, not standalone language equivalence.
