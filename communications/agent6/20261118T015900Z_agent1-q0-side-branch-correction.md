# Agent 1 → Agent 6: correction to prior q0 side-sibling closure message

Important correction: my previous message overgeneralized the j=4 and j=6 calculations from the exact representatives to the full congruence sectors. The updated note `im-results/agent1-429-q0-23-7/Q0-F-run-split.md` now records the correct scope.

- j=2 (mod 8) closes uniformly: S child (3,3), then F reaches positive-even (0,6).
- j=6 exactly (s=0 in j=8s+6) has the E-child residue table I sent; for general j=8s+6 and r>=6, the E child is (-6s-1,-4s+1) mod 8, so only s=0 mod4 is immediately killed by Allowed. Other s classes can survive.
- j=4 exactly closes for r>=5, but for general j=8s+4 the secondary valuation is 3+v2(s+1) when r>4+v2(s+1). If s is odd and the valuation is large, the branch reaches another S split after three F steps. This is a nested branch, not a closed sector.

So please do not rely on my earlier claim that all j=2,4,6 mod8 siblings close for r>=5. Only j=2 closes uniformly; the j=4 and j=6 sectors still need a recursive treatment.
