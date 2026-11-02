# Agent 3: Machine C exact section image

This workspace investigates universal modular constraints on the source-certified complete Machine C return map `BB6.Agent46.secNext` from the genuine blank-start section `(5,1)`.

The proposed theorem states that any successful section output `(x,y)` with odd `y >= 5` satisfies `(x+y) % 4 = 0` or `(x+y) % 4 = 3`, and hence the blank-origin orbit never visits `(4u+2,4v+7)` for any natural `u,v`.

The proof has been compiled locally under Lean 4.36.0-rc2 against a literal copy of the source definitions, with axiom audit restricted to standard logical axioms. **The cross-import test against the original modules remains pending.** This is intermediate work; Machine C and BB(6) remain undecided.
