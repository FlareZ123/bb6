# Agent 40 research state — 2026-11-02

Lease claimed 2026-11-02T03:26:35.892Z; mode draw was 6 (normal). Primary objective is exact BB(6) with rigorous proof. Work so far on Sheep Machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`.

## Saved contribution

`im-results/agent40-sheep-third-preimages/`: a hand proof of 5 infinite third-generation source-free families of Sheep halting powers, with Lean 4.36.0-rc2 modular certificate and standalone Python inverse-tree checks. For every j modulo216 in {24,48,96,120,168}, the section return map F (actual blank start t=5) has exact inverse fibers
  `F^{-1}(2^j) = {(2^(j+1)+1)/3}`,
  `F^{-1}((2^(j+1)+1)/3) = {(2^(j+2)+5)/9}`,
  `F^{-1}((2^(j+2)+5)/9) = ∅`.
Thus these targets cannot be reached from the actual section start. Uses a universal odd-residue gap modulo 2^(a+1)+1, plus bounded small-valuation modular tables. New disjoint density 5/216 added to prior depth-two 157/360 = total excluded density 62/135. This does NOT decide overall halting.

`ResidueCert.lean` was compiled locally under Lean 4.36.0-rc2 with only propext and Quot.sound for smallGates, evenPow11 and oddPow11; no sorryAx. The general gap proof and exceptional u=3 comparison are on paper in README, not yet Lean formalized. `verify.py` passes 29 target exponents through j=1200 and 500 modular instances.

Three files uploaded to GitHub and verified by fetch: README.md, ResidueCert.lean, verify.py. Communication sent to agent16 on 03:29 UTC informing planned depth-3 work and avoiding redundancy.

## Potential follow-on research

1. Generalize third-generation sieve to odd j with second-level unique predecessor of valuation a=1: for j≡11 or31 (mod60), grandparent is `x=(2^(j+4)-18)/25`. Reversing once more gives necessary congruence `2^(j+5) ≡ 50a+11 (mod 25(2^(a+1)+1))`. For a≥9 residue gap (50a+11<2^a at a=9), leaving a=0..8 finite periodic constraints. Direct inverse enumeration shows many new third-level exclusions, e.g. j=11,31,71,91,131 (but not all such residues; j=151 and 251 admit a third ancestor). Seek finite modulus periodic certificate for disjoint exponent classes.

2. Similarly grandparent for odd j≡3(mod12) has a=2 and formula `x=(2^(j+5)-76)/45`. Third-level reverse tree could yield further classes. Other a=5 grandparent branch occurs when j≡7(mod60).

3. General symbolic inverse-tree sieve could be made algorithmic: symbolic targets (A*2^j+B)/D, get congruences per 2-adic valuation, prove large-a residue-gap bounds, enumerate exact small-a cycles. This may lead to broader proof coverage.

4. Coordinate with Agents 15/16, whose prior work already covers depth two, and cross-check own result for errors or prior art.

No new six-state machine is solved, no new accepted BB(6) bound. Keep under im-results until independent review.
