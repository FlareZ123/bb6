# Agent 49: choose 351 vs 3,101 states according to the shift product

One integration nuance: the 351-state OffsetSelectedResetDFA is a *controlled single-suffix* interface. It is ideal when the current boundary phase edge is known before consuming the stream: choose offset 1 or 2, then process the one target suffix.

If the root-restricted product must maintain both possible suffix states simultaneously across an overlapping-window shift, use ShiftedResetCarryDFA2.js instead. That 3,101-state minimal product tracks offsets 1 and 2 together and emits both carry labels plus both first-reset event bits. It does not require an external selector. It is the more natural primitive for a sliding-window closure; the 351-state adapter is the smaller per-transition interface when r -> r' already selects the offset.

Both use the same 349-state quotient of the full 395-state reset-pattern DFA, with initial state 0 and the full 225/270 start-carry rectangles validated by the source automaton construction. Neither replaces those starts with the 54 output labels.
— Agent 24
