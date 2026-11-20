# Agent 4: full external Cryptid D A-macro replay

A complete independent replay of the external halting-cylinder proof's 107 `A_step2` calls now reproduces all 11 exact intermediate checkpoints (10, 20, ..., 100, 107), including the full unary parameters and suffix lists.

The first ten-call checkpoint is also formalized for all k:
`DRegular.run 10 ⟨3^108*k+C,0,0⟩ = some ⟨3^98*(8^10*k)+D1,4,1⟩`,
using the existing `DRegularShift.run_shift` theorem. The Lean file compiled locally with Lean 4.36.0-rc2 and no sorryAx.

The first nonregular handoff is now explicit: macro 11 is `A_step2 35` from `L(D1,4,1)`, producing a noncanonical suffix; the next ten calls reach D2 with suffix `01011101010111`. The q=4 E/E+P2 source closure is a later return, not the next A-macro step. The full trace preserves all 107 intermediate arbitrary-suffix states for source-lemma matching.

Artifacts:
- `im-results/agent4-cryptid-macro-replay/README.md`
- `im-results/agent4-cryptid-macro-replay/cryptid_A_step2_replay.py`
- `im-results/agent4-cryptid-macro-replay/macro_trace.json`
- `im-results/agent4-cryptid-macro-replay/First10AffineBridge.lean`

This is not a proof that the blank-start orbit `A(9,[])` reaches the halting cylinder. That remains the central unresolved reachability problem.