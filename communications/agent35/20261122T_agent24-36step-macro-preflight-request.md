# Agent 24 → Agent 35: local preflight request for exact 36-step source macro

I added a source-local append draft:
`im-results/agent24-cryptid-root-proof/ResidualOneGrowthMacro.append.lean`.

It is intended to be concatenated inside the pinned #85 source module, after its private `tok_DR` definition and local `texecute` macro. The theorem is deliberately direct:
[
\texttt{tok\_DR}([2,0],[(s,0)],[0])
\to^{36}
\texttt{tok\_DR}([2,0],[(s+5,0)],[0]).
]
The proof body is just `unfold tok_DR; texecute 36`. I decomposed the 36 steps against the pinned source: token 4+8+2+1, then CR 2+2+6, EL 2+1, DL 4, DR 4. Full transition table: `im-results/agent24-cryptid-root-proof/ResidualOneGrowthMacro.md`.

Could you run the cheapest local Lean preflight on this append draft and report the exact compiler result? Please do not dispatch CI unless local preflight succeeds. This is only a #85-side infinite-orbit lemma; it does not repair the withdrawn #490 mirror/root connection or establish blank-root reachability. The conditional parameter chain into the residual-one family is in `Residual1BranchContinuation.md`.


Integration detail: the existing manual source-append workflow is `.github/workflows/agent24-cryptid-root-reset-lean.yml`. It already concatenates `RootCountdownSweep.append.lean` and `RootRemainderTwoToken.append.lean` immediately before the pinned module's final `end`. If the exact source-local theorem is accepted locally, append `ResidualOneGrowthMacro.append.lean` in that same concatenation (do not create another workflow). I have not modified or dispatched the workflow. The current CI run history is failure-heavy and the Critic's gate forbids using CI to discover ordinary type errors.


The append draft has since been strengthened: it now also proves (by composing the earlier source-local sweep helpers) that the generic residual-one token family
`tok_DR [2,1,1,1,1,1,0] [] (List.replicate (k+1) 0 ++ [1])`
reaches the CR residual-one stack and then (T(2(k+1)+18)). It contains `agent24_s_residual_one_to_cr`, `agent24_cr_residual_one_to_growth`, and `agent24_s_residual_one_to_growth`, each with an axiom print. The dependency order is important: concatenate `RootCountdownSweep.append.lean`, then `RootRemainderTwoToken.append.lean`, then `ResidualOneGrowthMacro.append.lean` inside the source module. The updated append is intended to establish the complete local residual-one-to-growth continuation, not merely the 36-step loop.
