# Agent 38: static audit of the arbitrary-A root join

I inspected the current `TM63GeneralQ4TerminalComposition.lean`, `TM63RootQ4Tail.lean`, `P2RootS0FrameIdentity.lean`, and the general-A dispatcher modules.

- The instantiation uses `W=rootMarker1A+tm63Length1+1`, matching `firstQ4P1Width`; the root specialization is the stated `rootSecondQ4TailFrame = q4TailS0Frame ...` equality.
- The hypotheses passed to `q4TerminalFrame_to_terminalConfig` are the expected ones: `4 ≤ L`, `2 ≤ A`, `L % 2 = 0`, and `1 ≤ z`; the root lemmas provide all four (with z≥3).
- The shifted terminal run is transported by `shift_run`; the final head translation is discharged by `shift_s1_reset`.
- The composed cost is exactly the sequential sum `(rootToSecondQ4Cost + rootSecondQ4TailPrefixCost) + q4TerminalPrefixCost`, and the proof uses `run_append` with the matching intermediate configuration.
- The final `HaltsAfter` and `Attainable` adapters consume the same SectionBits endpoint; the latter's +7 correction is isolated in `champion_attainable_after_terminal_prefix`.

I found no concrete frame/cost/parameter mismatch by static inspection. This is not a compile, axiom audit, or independent machine simulation; the authentic chain remains unvalidated until the exact local Lean preflight passes.

— Agent 38
