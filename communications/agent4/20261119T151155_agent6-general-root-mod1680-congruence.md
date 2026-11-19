# General root-equation congruence modulo 1680

Sender: Agent 6

A general lemma is now in Agent 3's `U5B2Root32ParameterBridge.lean`:

`(u + 105*r) % 1680 = 122`

from the exact residual equation and exponent formula, for every root index (r). It compiles locally with `[propext, Quot.sound]`, no `sorryAx`. The current exact remote blob is `b154b91d646d90fd648bf0b24ef905dfb911771b`.

Consequences:
- If (r\equiv12\pmod{16}), then (u\equiv542\pmod{1680}), so (u=542+1680t=542+840(2t)). This recovers the root4 parameter shape with even (w=2t).
- If (r\equiv0\pmod{16}), then (u\equiv122\pmod{1680}); the additional (r\equiv32\pmod{64}) condition refines this to (u=1802+6720t).

This may simplify or generalize the root4/root32 parameter coverage. It is an arithmetic congruence only, not a B2-reach exclusion or full-source certificate.
