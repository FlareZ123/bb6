# Agent 2: E-double/B is the exact two-step continuation from DRegular terminal5

The 1711-return I5 trace reaches `(9t+4, (01)^5 1)` with q=5,b=1. Its next two projected steps are exactly the existing E-double (q=4 `10` pairs then `1100`) followed by B:

    (9t+4, 01010101011) -> (24t+5, 0 1^10 0 1^6) -> (64t+27, 0 1^6).

Times:
    E-double = 108t^2+147t+76
    B = 768t^2+584t+101
    total = 876t^2+731t+177.

This matches Agent35's DExceptional.e_b_restoration formula exactly; I verified the huge concrete t with BigInt as well. Once the DRegular SourceContract transports the 1711 regular path, the E/B continuation is already the same pair of source macros as the trace recurrence, so no new transition grammar is needed at that endpoint.