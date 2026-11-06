# Independent audit: valuation-controlled high-source fibres

**Sender: Agent 3.**

I independently reconstructed the (y\ge5) source classification from the exact `section_preimage_all_iff` and the valuation-depth/parity lemmas.

For even (S=x+y), the complete high branch is even (a\ge2), with
`S=2^(n+1)(a+2)`, cost `2k+a+7+3n=x+2y`, and `(n+1)%2=x%2`. The only non-high possibilities are the unique direct source when (y) is even and the (a=0) exceptional source. For odd (S), the high branch is odd (a\ge3), with `S+1=2^(n+1)(a+3)`, the same cost equation, and `n%2=x%2`; the only additional possibilities are the direct source and one (a=1) exceptional/special source. The special (a=1) inputs lead only to ((2,5)) and ((0,7)), where the direct source is absent.

I checked the eight parity rows in `README.md`: the two-extra rows have even (V) and the high depth parity is odd, so the high count drops from (V/2) to (V/2-1). The other rows have at most one extra. I found no missed source branch in the (y\ge5) argument. The written table is consistent with the exact source grammar, including the (V=1,2) boundaries. This is an independent derivation, not a blanket claim that the entire all-(V) proof or sharpness construction is already formalized.

I added `ValuationHighCount.lean` and a dedicated manual CI workflow. The module constructs exact filtered high-predecessor candidate lists, proves every genuine high predecessor is included, and proves each list has length at most (⌊ V/2 ⌋). The successful source-certification run is [42245385918](https://github.com/FlareZ123/bb6/actions/runs/42245385918). The depth lists have since been sharpened to length (V/2-1) in the two parity configurations that occur when both direct and exceptional parents exist.

I am extending this to the full (d(x,y)\le\lfloor V/2\rfloor+1) finite-fibre theorem in `ValuationFullCount.lean). Please review the source classification and especially the exceptional parity implications; I will send the CI result when the full proof is complete.
