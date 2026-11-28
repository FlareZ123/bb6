# Agent24 late CI state (automatic metadata snapshot)

Generated UTC 2026-11-28T01:42:24.548Z, immutable lease age 63.47 minutes.

## Depth-three matrix

- [run 46093644994](https://github.com/FlareZ123/bb6/actions/runs/46093644994) — queued, not concluded, 2026-11-28T01:32:50Z

## Recent manual proof targets (do not infer inputs from title)

- [run 46094260926](https://github.com/FlareZ123/bb6/actions/runs/46094260926) — title "Agent38 M62 source check: raw45-hard-d3-b", status queued, conclusion not concluded, created 2026-11-28T01:40:11Z
- [run 46094256684](https://github.com/FlareZ123/bb6/actions/runs/46094256684) — title "Agent38 M62 source check: raw45-hard-d3-a", status queued, conclusion not concluded, created 2026-11-28T01:40:09Z
- [run 46094252660](https://github.com/FlareZ123/bb6/actions/runs/46094252660) — title "Agent38 M62 source check: raw45-d3-ngram", status in_progress, conclusion not concluded, created 2026-11-28T01:40:06Z
- [run 46093725774](https://github.com/FlareZ123/bb6/actions/runs/46093725774) — title "Agent38 M62 source check: raw45-exact96", status completed, conclusion failure, created 2026-11-28T01:33:46Z
- [run 46093486193](https://github.com/FlareZ123/bb6/actions/runs/46093486193) — title "Agent38 M62 source check: raw45-exact96", status completed, conclusion failure, created 2026-11-28T01:30:59Z
- [run 46093481756](https://github.com/FlareZ123/bb6/actions/runs/46093481756) — title "Agent38 M62 source check: raw45-cut-assembled", status completed, conclusion success, created 2026-11-28T01:30:55Z
- [run 46093478077](https://github.com/FlareZ123/bb6/actions/runs/46093478077) — title "Agent38 M62 source check: raw45-b1la-a1lc-cut", status completed, conclusion success, created 2026-11-28T01:30:53Z


### Failed run 46093725774

```text
2026-11-28T01:35:19.6428947Z [lean-closure] level 19: 1 module(s)
2026-11-28T01:35:19.6431058Z [lean-closure] compiling Raw45Exact96 <- im-results/agent24-raw45/Raw45Exact96.lean
2026-11-28T01:35:20.6129067Z Raw45Exact96.lean:14:59: error: unsolved goals
2026-11-28T01:35:20.6129399Z case inr.inr.inr.inl.false
2026-11-28T01:35:20.6129604Z v : Transition
2026-11-28T01:35:20.6129818Z hv : some { write := true, right := false, next := 3 } = v
2026-11-28T01:35:20.6130488Z ⊢ (match ↑3, false with
2026-11-28T01:35:20.6131172Z     | 0, false => some { write := true, right := true, next := 1 }
2026-11-28T01:35:20.6131475Z     | 0, true => some { write := false, right := false, next := 2 }
2026-11-28T01:35:20.6131772Z     | 1, false => some { write := true, right := true, next := 2 }
2026-11-28T01:35:20.6132076Z     | 1, true => some { write := false, right := false, next := 0 }
2026-11-28T01:35:20.6132384Z     | 2, false => some { write := false, right := true, next := 3 }
---
2026-11-28T01:35:20.6139057Z     | x, x_1 => none) =
2026-11-28T01:35:20.6139227Z     v
2026-11-28T01:35:20.6139527Z 'BB6.Agent24Raw45Exact96.witness_fits' depends on axioms: [propext, sorryAx, Quot.sound]
2026-11-28T01:35:20.6140100Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6140827Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6141504Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6151083Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:35:20.6312883Z ##[error]Process completed with exit code 1.
2026-11-28T01:35:20.6398146Z Post job cleanup.
2026-11-28T01:35:20.6990462Z [command]/usr/bin/git version
2026-11-28T01:35:20.7028375Z git version 2.56.1
2026-11-28T01:35:20.7058651Z Temporarily overriding HOME='/home/runner/work/_temp/f2c1dc36-46c1-4a58-a570-0f9d613234d7' before making global git config changes
---
2026-11-28T01:35:20.6139227Z     v
2026-11-28T01:35:20.6139527Z 'BB6.Agent24Raw45Exact96.witness_fits' depends on axioms: [propext, sorryAx, Quot.sound]
2026-11-28T01:35:20.6140100Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6140827Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6141504Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6151083Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:35:20.6312883Z ##[error]Process completed with exit code 1.
2026-11-28T01:35:20.6398146Z Post job cleanup.
2026-11-28T01:35:20.6990462Z [command]/usr/bin/git version
2026-11-28T01:35:20.7028375Z git version 2.56.1
2026-11-28T01:35:20.7058651Z Temporarily overriding HOME='/home/runner/work/_temp/f2c1dc36-46c1-4a58-a570-0f9d613234d7' before making global git config changes
2026-11-28T01:35:20.7059343Z Adding repository directory to the temporary git global config as a safe directory
---
2026-11-28T01:35:20.6140100Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6140827Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6141504Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:35:20.6151083Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:35:20.6312883Z ##[error]Process completed with exit code 1.
2026-11-28T01:35:20.6398146Z Post job cleanup.
2026-11-28T01:35:20.6990462Z [command]/usr/bin/git version
2026-11-28T01:35:20.7028375Z git version 2.56.1
2026-11-28T01:35:20.7058651Z Temporarily overriding HOME='/home/runner/work/_temp/f2c1dc36-46c1-4a58-a570-0f9d613234d7' before making global git config changes
2026-11-28T01:35:20.7059343Z Adding repository directory to the temporary git global config as a safe directory
2026-11-28T01:35:20.7059826Z [command]/usr/bin/git config --global --add safe.directory /home/runner/work/bb6/bb6
2026-11-28T01:35:20.7096594Z [command]/usr/bin/git config --local --name-only --get-regexp core\.sshCommand
```

### Failed run 46093486193

```text
2026-11-28T01:33:19.6853409Z [lean-closure] level 19: 1 module(s)
2026-11-28T01:33:19.6855516Z [lean-closure] compiling Raw45Exact96 <- im-results/agent24-raw45/Raw45Exact96.lean
2026-11-28T01:33:20.2522044Z Raw45Exact96.lean:17:3: error: unknown tactic
2026-11-28T01:33:20.2522648Z Raw45Exact96.lean:14:59: error: unsolved goals
2026-11-28T01:33:20.2523065Z v : Transition
2026-11-28T01:33:20.2523305Z q : Fin 6
2026-11-28T01:33:20.2523646Z b : Bool
2026-11-28T01:33:20.2523916Z hv : parent (q, b) = some v
2026-11-28T01:33:20.2524460Z ⊢ witness (q, b) = v
2026-11-28T01:33:20.2525134Z 'BB6.Agent24Raw45Exact96.witness_fits' depends on axioms: [propext, sorryAx]
2026-11-28T01:33:20.2525653Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2526230Z Raw45Exact96.lean:39:36: error: Expected type must not contain free variables
---
2026-11-28T01:33:19.6855516Z [lean-closure] compiling Raw45Exact96 <- im-results/agent24-raw45/Raw45Exact96.lean
2026-11-28T01:33:20.2522044Z Raw45Exact96.lean:17:3: error: unknown tactic
2026-11-28T01:33:20.2522648Z Raw45Exact96.lean:14:59: error: unsolved goals
2026-11-28T01:33:20.2523065Z v : Transition
2026-11-28T01:33:20.2523305Z q : Fin 6
2026-11-28T01:33:20.2523646Z b : Bool
2026-11-28T01:33:20.2523916Z hv : parent (q, b) = some v
2026-11-28T01:33:20.2524460Z ⊢ witness (q, b) = v
2026-11-28T01:33:20.2525134Z 'BB6.Agent24Raw45Exact96.witness_fits' depends on axioms: [propext, sorryAx]
2026-11-28T01:33:20.2525653Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2526230Z Raw45Exact96.lean:39:36: error: Expected type must not contain free variables
2026-11-28T01:33:20.2526609Z   0 ∈ delays (zeroNext m) 0
---
2026-11-28T01:33:20.2523916Z hv : parent (q, b) = some v
2026-11-28T01:33:20.2524460Z ⊢ witness (q, b) = v
2026-11-28T01:33:20.2525134Z 'BB6.Agent24Raw45Exact96.witness_fits' depends on axioms: [propext, sorryAx]
2026-11-28T01:33:20.2525653Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2526230Z Raw45Exact96.lean:39:36: error: Expected type must not contain free variables
2026-11-28T01:33:20.2526609Z   0 ∈ delays (zeroNext m) 0
2026-11-28T01:33:20.2526771Z 
2026-11-28T01:33:20.2526991Z Hint: Use the `+revert` option to automatically clean up and revert free variables
2026-11-28T01:33:20.2527508Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528088Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528735Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:33:20.2776968Z ##[error]Process completed with exit code 1.
---
2026-11-28T01:33:20.2524460Z ⊢ witness (q, b) = v
2026-11-28T01:33:20.2525134Z 'BB6.Agent24Raw45Exact96.witness_fits' depends on axioms: [propext, sorryAx]
2026-11-28T01:33:20.2525653Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2526230Z Raw45Exact96.lean:39:36: error: Expected type must not contain free variables
2026-11-28T01:33:20.2526609Z   0 ∈ delays (zeroNext m) 0
2026-11-28T01:33:20.2526771Z 
2026-11-28T01:33:20.2526991Z Hint: Use the `+revert` option to automatically clean up and revert free variables
2026-11-28T01:33:20.2527508Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528088Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528735Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:33:20.2776968Z ##[error]Process completed with exit code 1.
2026-11-28T01:33:20.2881599Z Post job cleanup.
---
2026-11-28T01:33:20.2525134Z 'BB6.Agent24Raw45Exact96.witness_fits' depends on axioms: [propext, sorryAx]
2026-11-28T01:33:20.2525653Z 'BB6.Agent24Raw45Exact96.exact_weighted_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2526230Z Raw45Exact96.lean:39:36: error: Expected type must not contain free variables
2026-11-28T01:33:20.2526609Z   0 ∈ delays (zeroNext m) 0
2026-11-28T01:33:20.2526771Z 
2026-11-28T01:33:20.2526991Z Hint: Use the `+revert` option to automatically clean up and revert free variables
2026-11-28T01:33:20.2527508Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528088Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528735Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:33:20.2776968Z ##[error]Process completed with exit code 1.
2026-11-28T01:33:20.2881599Z Post job cleanup.
2026-11-28T01:33:20.3529404Z [command]/usr/bin/git version
---
2026-11-28T01:33:20.2526771Z 
2026-11-28T01:33:20.2526991Z Hint: Use the `+revert` option to automatically clean up and revert free variables
2026-11-28T01:33:20.2527508Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528088Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528735Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:33:20.2776968Z ##[error]Process completed with exit code 1.
2026-11-28T01:33:20.2881599Z Post job cleanup.
2026-11-28T01:33:20.3529404Z [command]/usr/bin/git version
2026-11-28T01:33:20.3563748Z git version 2.56.1
2026-11-28T01:33:20.3589200Z Temporarily overriding HOME='/home/runner/work/_temp/ecf6e0fa-eee1-448f-bb56-b29eb5cd0ec8' before making global git config changes
2026-11-28T01:33:20.3590365Z Adding repository directory to the temporary git global config as a safe directory
2026-11-28T01:33:20.3593167Z [command]/usr/bin/git config --global --add safe.directory /home/runner/work/bb6/bb6
---
2026-11-28T01:33:20.2526991Z Hint: Use the `+revert` option to automatically clean up and revert free variables
2026-11-28T01:33:20.2527508Z 'BB6.Agent24Raw45Exact96.all_halting_scores_le_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528088Z 'BB6.Agent24Raw45Exact96.exact_blank_step_96' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
2026-11-28T01:33:20.2528735Z [lean-closure] ERROR: Command '['lean', '-o', '/tmp/agent38-m62/Raw45Exact96.olean', 'Raw45Exact96.lean']' returned non-zero exit status 1.
2026-11-28T01:33:20.2776968Z ##[error]Process completed with exit code 1.
2026-11-28T01:33:20.2881599Z Post job cleanup.
2026-11-28T01:33:20.3529404Z [command]/usr/bin/git version
2026-11-28T01:33:20.3563748Z git version 2.56.1
2026-11-28T01:33:20.3589200Z Temporarily overriding HOME='/home/runner/work/_temp/ecf6e0fa-eee1-448f-bb56-b29eb5cd0ec8' before making global git config changes
2026-11-28T01:33:20.3590365Z Adding repository directory to the temporary git global config as a safe directory
2026-11-28T01:33:20.3593167Z [command]/usr/bin/git config --global --add safe.directory /home/runner/work/bb6/bb6
2026-11-28T01:33:20.3627093Z [command]/usr/bin/git config --local --name-only --get-regexp core\.sshCommand
```
