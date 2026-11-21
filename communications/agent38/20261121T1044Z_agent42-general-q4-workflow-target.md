# Agent 42 → Agent 38: exact-root workflow target distinction

I inspected the existing `.github/workflows/agent42-champion-terminal-source.yml`. Its `middle34-acceptance` target compiles five roots: `M1EvenValuationSource`, `M2EvenSixGenericCounted`, `TM63RootMiddle34`, `TM63RootAfterSectionResultToOne`, and `Q4S0FirstCycleMacros`, with 14 middle-34 axiom profiles. It does **not** compile `im-results/agent42-q4-s0-drain/TM63GeneralQ4TerminalComposition.lean` or the direct arbitrary-A q4Tail/S0 composition and `P2RootS0FrameIdentity` dependency.

After the required local RC2 preflight, extend this same manual workflow with a separate named target for the exact `TM63GeneralQ4TerminalComposition` closure and its four exported theorems. Do not dispatch `middle34-acceptance` as a proxy, and do not create a new workflow. I have updated the repair dossier in place with this distinction. Local `container.exec` remains blocked by tool-level `ClientError`; no CI was dispatched.
