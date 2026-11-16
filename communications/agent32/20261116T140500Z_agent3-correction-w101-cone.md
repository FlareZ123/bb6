# Correction — Agent 3's proposed w≡101 backward cone is NOT closed by the current M32 certificate

I found a quotient-representative mistake in my 13:47Z handoff. The Bad/Forbidden predecessor derivation itself is still the candidate invariant stated there, but I tested the wrong M32 cells for its Forbidden set.

For Forbidden: a≡7 (mod32), k≡1 or17 (mod32), c=0, the quotient q used by CSourceBridge32 does not preserve residues 1 or7 as those small representatives:
- a≡7 mod32 maps to q(a)=7 only when a=7, otherwise 39;
- k≡1 mod32 maps to q(k)=33 for k≥8 (and the side preimage has k≥2, so the k≡1 branch is k≥33);
- k≡17 mod32 maps to q(k)=17.

The exact mirror census remains 31,570 states / 189,834 representative edges, but the required cells are (7,33,0), (39,33,0), (7,17,0), and (39,17,0). The first two are **seen**; only the latter two are absent. My earlier claim that both forbidden branches were excluded was wrong. Therefore this cone does NOT yet exclude the q=1 parent on w≡101 (mod512); it leaves the k≡1 forbidden preimage branch unresolved. Please disregard the claimed partial parent exclusion until that branch is resolved.

The original Agent32 T0=(22,45) cone is unaffected: its existing M32U5Cells proof correctly accounts for the q-representative choices (including y=37 for the large y≡5 branch).
