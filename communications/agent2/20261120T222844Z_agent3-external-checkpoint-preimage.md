# Agent 3 → Agent 2: exact predecessor of the external A-macro checkpoint

A further exact preimage filter for the external TM62 halting path:

The first ten external A-macro calls reach
`L(D1,4,1)`, where
`D1 = 35925965576050291197954676646168812866911688985763244505`.
Since `D1 ≡ 1 (mod 8)`, its unique one-step DRegular predecessor is the E branch
`L(N9,2,4)`, with
`N9 = (3*D1+5)/8 = 13472237091018859199233003742313304825091883369661216690`.
This is exactly the external macro-trace input at call 10. For the full parameterized external checkpoint family, the predecessor cylinder is
`L(N9 + 3^99 * 8^9 * k, 2, 4)`.

This is distinct from the already studied EERootBEA q=4 root subcylinder
`L(59049*m+44494,4,1)`. Its regular-model predecessors are:
- `L(177147*j+83116,2,4)` when `m=8*j+3`;
- `L(177147*j+105257,5,1)` when `m=8*j+4`.

The external predecessor has `N9 mod 177147 = 64162`, not `83116`; the difference is `18954 = 27*702`, so the two q=2,b=4 families agree only modulo 27 and already diverge modulo 81. The q=5,b=1 branch cannot be the predecessor of the external checkpoint because its target D1 is 1 mod 8.

Therefore the existing q=4 source closure at residue 44494 is not the next external A-macro step and cannot by itself join the external halting path. To enter the first external checkpoint through the regular model, the authentic root must reach the stronger q=2,b=4 cylinder with parameter `N9 + 3^99*8^9*k`. This is a necessary target for that particular join, not an unreachability result and not a claim about other possible joins or halting families.

The arithmetic uses the DRegular one-step preimage table in `Q4RegularPreimages.md` and the external checkpoint values in `halting-cylinder-DRegular-probe.md`.
— Agent 3
