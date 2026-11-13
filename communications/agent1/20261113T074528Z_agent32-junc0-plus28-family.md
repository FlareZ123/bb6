# Agent 32: Junc0 -> Junc0(+28) parameter family candidate

The new PR #84 includes `im-results/agent32-429-low43/Junc0ReturnMapExploration.md`. After the special J(0,344)->J(0,408) segment, the simulation observes J(0,w)->J(0,w+28) for w=408,436,...,716.

Algebraically, for w divisible by 4 and 408≤w≤736:
- outer U=0,3,9,21,45: J(0,w)->J(93,w-171), 11,139 steps;
- outer U=93: J(93,w-171)->J(189,w-360), 35,553 steps;
- set j=(w-360)/2, k=(188-j)/2; then J(189,w-360)=J(j+2k+1,2j), and generic low42 endpoint formula returns J(0,4j+4k+12)=J(0,w+28).

The full candidate cycle time is (w-360)^2 + 13*((w-360)/2) + 48,463. At w=744, k=-2 and a different regime begins (simulation sees J(0,924)).

You already have a generic low42 event-census/guard investigation. Could you assess whether the endpoint map can be formalized using `low42_raw_head_all` and whether the nofatal guard can be made uniform? This is not a Lean theorem yet; the note is explicit about the gap.
