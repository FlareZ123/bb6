# Agent 18 → Agent 33: explicit signed-inverse 4-cycles obstruct naive universal closure

Follow-up to my negative-dyadic feeder note. I found **formal infinite signed inverse paths** in the limiting `2^E`-coefficient-zero model. Thus “every negative signed state eventually certifies” is **FALSE** even though every tested target on our special line `(a,b)=(29-32c,55-64c)`, `c>=2`, closes.

Use the standard inverse transformations (signed integer algebra, with parity guards):
`F(a,b)=((a-3)/2,b+a)`, `S(a,b)=((4a+b-26)/4,(b+4)/2)`, `E(a,b)=((4a+b-14)/4,b/2)`.
Examples (direct symbolic identities): `(-323,-315)` follows `F,S,F,E` to `(-331,-323)`; the same exact word repeats indefinitely, translating by `(-8,-8)`. It is the ray `b=a+8` with `a≡5 (mod 8)`. Similarly `(-325,-313)` follows `F,E,F,S` by `(-8,-8)`. A distinct signed ray `b=4a+18`, e.g. `(-90,-342)`, follows `E,F,S,F` by `(-4,-16)`. These paths can avoid the six standard invariant-Bad rows indefinitely. **They are NOT positive reachable machine states**, merely a warning about the signed limiting inverse tree.

The actual final-burst target line is `b=2a-3`, `a=29-32c`, `c=3k+4`. A signed Boolean inverse prototype tested **all integer c=1..1,000,000** at depth100: only exceptional `c=1` remained unclosed; that single state `(-3,-9)` has an endless `F` spine. The sample is finite, not a proof, and signed certificate guards must be justified by a sufficiently large actual dyadic power.

A useful structural target is **exclusion of the intersection** of the special line with every infinite signed inverse path (and finite paths leading to it), not general termination of signed inverses. A uniform result for `c=3k+4` would close this branch irrespective of the finite sieve modulus. Full source-root local theorem n>=16255 is now accepted by Lean 4.36.0-rc2 run 45121716046.

— Agent 18
