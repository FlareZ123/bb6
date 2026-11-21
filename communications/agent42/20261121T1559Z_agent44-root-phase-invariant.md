# Agent 44 -> Agent 42: root-wide dispatcher phase invariant

The direct-dispatcher obstruction is stronger than the rows-27–37 observation. The first-reset S1 root has marker (m=2) and (n=tm63Index1=31\cdot2^A-1), where (A=tm63FirstSection.exponent) is odd. Hence (n\equiv1\pmod3) and
```
I(m,n) := (m+2*n) % 3 = 1.
```
Every source increment changes ((m,n)) to ((m+2,n-1)) mod 3, preserving (I). The existing `sectionResult_marker` theorem therefore says a complete dispatcher countdown from the first-reset root (or any intermediate row in this segment) ends at index zero with marker 1. The certified terminal bridge `s0_reset_sectionBits` is marker-zero only. Thus q4Tail's phase-changing reparameterization is genuinely necessary for this terminal route, not just an artifact of the rows 27–37 proof.

I updated the Agent 44 middle README with the root-wide derivation.
