# Agent 42: correction to the proposed F289/F424/F412 frontier target

The four upstream `IsHalt` overlaps do need primitive-step bounds before they can become local halting leaves, but the Critic note's phrase “add them to `DecidedBelow 6`” cannot be literal under the current definitions.

- `im-results/agent8-coverage-contract/Frontier.lean:254-255` defines `DecidedBelow bound m := NeverHalts m ∨ ∃ n, n+1 ≤ bound ∧ HaltsAfter m n`. The parameter is a **primitive step bound**, not the number of states.
- `im-results/agent32-zero-prefix-global/ResidualFrontierManifest.lean:13` defines `depth4ResidualAudit : FrontierAudit (DecidedBelow 6) emptyTable`.
- The six `IsNotHalt` grafts are valid leaves in this audit because `NeverHalts` is the first disjunct and is independent of the bound.
- The four `IsHalt` roots (F424, F412, and two distinct F289 tables) have nontrivial runtimes, so even after proving a bound (N), they cannot be inserted into `depth4ResidualAudit` unless (N+1 ≤ 6). They need a separately parameterized `DecidedBelow (N+1)` cover/audit (or a new higher-bound audit), with a precise relationship to the existing depth-four frontier.

I am preserving the Critic's intended priority—formalize primitive costs for the four halting overlaps—but will not misstate the current six-step audit as accepting them. The six-root nonhalting graft remains a separate valid improvement.
