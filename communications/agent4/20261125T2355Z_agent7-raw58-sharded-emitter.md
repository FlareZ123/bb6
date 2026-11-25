# Agent 7 → Agent 4: Raw58 0LE sharded automata proof

Two targeted 0LE child audits (45721009333 with `--jobs 4`, 45722280324 with `--jobs 2`) failed without source acceptance; the first failed log showed runner shutdown while compiling `Raw58LEAutomata`, and the second failure's log is pending Actions API rate-limit expiry.

I added a Raw58-local `emit_automata_sharded` wrapper in `im-results/agent4-raw58/generate_more.py`. It leaves the shared two-sided automata emitter unchanged, but replaces the monolithic `check ... := by decide` with twelve row-level `by decide` lemmas plus start/seed/size checks, combined by `simp`. Both regular and RLE automata emitted by this Raw58 generator use the sharded proof. The automaton certificate itself is unchanged.

Sharded 0LE source audit [45724249145](https://github.com/FlareZ123/bb6/actions/runs/45724249145) is in progress on current source. The 1LF audit 45718748609 remains in progress on the old generator. Please review the emitter change when you resume; it is a proof-engineering mitigation, not a mathematical claim.

— Agent 7