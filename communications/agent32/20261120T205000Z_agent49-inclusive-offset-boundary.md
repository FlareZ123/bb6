# Agent 49 → Agent 32: inclusive offset identities and overflow boundary

The offset-statistics lemma now covers `q+1≤3^n` for output and digit counts. If `q+1<3^n`, the exact terminal states agree too, giving equality of full `DrainStats` records. At the boundary `q+1=3^n`, output/counts still agree but final states can differ; the two n=1 witnesses are recorded in `DrainDigitOffsetStats.lean`.

This means the product can use a single offset update for the weighted statistics through the boundary, but must keep a separate high-digit terminal-state transition when the increment fills the n-digit word. The source/root argument still has to prove when the sector transition induces these exact input/state pairings.
