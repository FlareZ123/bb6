# Agent 4: strictly increasing rank for the exact P1 acceleration

Status: **source-verified structural result**, independent of finite numerical simulation and of all P1 residue-cone exclusions. Both modules compile against the original unmodified `im-results/agent1-p1-map/PosEvenForm.lean` on Lean 4.36.0-rc2. Verification: [manual CI 41436787367](https://github.com/FlareZ123/bb6/actions/runs/41436787367) for `Rank.lean`; [manual CI 41437507896](https://github.com/FlareZ123/bb6/actions/runs/41437507896) for `RankDecision.lean` before the additional no-cycle lemma. CI for its latest no-cycle update has been dispatched. Kernel audits report only `[propext, Quot.sound]`, no `sorryAx`.

## Authentic map and rank

This concerns machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, using the authentic Agent 1 acceleration `BB6.Agent1.G`, `BB6.Agent1.T`, and blank-entry predicate `BB6.Agent1.Reach` from `PosEvenForm.lean`.

In `Rank.lean`:

- `G_sum_growth`: for all natural k,c, (2k+c+2 \le \mathrm{fst}(G(k,c))+\mathrm{snd}(G(k,c))).
- `G_one_growth`: (2k+4<\mathrm{fst}(G(k,1))+\mathrm{snd}(G(k,1))).
- **`T_sum_growth`: every defined accelerated transition `T a c = some (b,d)` satisfies `a+c < b+d`.** This is a global, all-state Lyapunov function, not a statement restricted to computed samples.
- `reach_bounded_trace`: if `Reach a c`, there exists an exact n-transition path `Iter n 2 1 a c` satisfying `n+3 ≤ a+c`.

In `RankDecision.lean`:

- A total executable trajectory `run n`, where `none` propagates after halting.
- `reach_iff_bounded_run`: `Reach a c ↔ ∃n, n+3≤a+c ∧ run n=some(a,c)`.
- The constructive `reach_decidable` instance supplies `Decidable (Reach a c)` for every fixed pair by searching `Fin (a+c+1)`. Its completeness is derived from the strict rank rather than heuristic cutoff.
- `iter_rank_growth` and `no_positive_cycle`: every n-step path grows rank by at least n; no positive-length accelerated path can revisit its starting pair. The no-cycle extension is undergoing final source CI verification.

The recursion's difficult branch uses strong induction on k, and the c=3 branch requires the separate `G_one_growth` lemma. This circumvents the false naive idea that every branch follows directly from `G_sum_growth` with unchanged coefficients.

## Exact significance and limitations

For **each fixed target** (a,c), reachability from blank is constructively decidable with a horizon at most a+c−3. In particular, individual critical-gateway searches can be made logically complete with that enormous bound. This is useful as a proof-search kernel and soundness check for experimental heuristics.

The P1 halting criterion quantifies over the **unbounded** critical family `(2, 14*2^n-2*n-10)`. Our state-specific search bounds grow exponentially with n and do **not** yield a uniform bound on n or decide P1 halting. Strict rank growth also allows infinite nonperiodic orbits, so it does **not** imply nonhalting. Existing source-proved index-family exclusions remain essential. No BB(6) bound or machine decision is asserted.

The modules live in `im-results/` until a global closure theorem is obtained; they are not promoted to `results/`.

## Next questions

1. Can the rank be sharpened to a monotone arithmetic invariant excluding the *entire* residual critical-index classes n≡2,14 (mod16)?
2. Since forward rank strictly increases, can a finite-state abstraction of rank, counter parity, and G's exact shifted-power valuation yield an inductively closed forward reachability language?
3. Can bounded-run soundness be used as an adversarial regression checker for claimed inverse-cone certificates with small fixed target ranks?

Use `.github/workflows/agent4-p1-cone2398.yml`, manually dispatched, to recheck original-source modules with the new proofs. No per-commit CI is configured.
