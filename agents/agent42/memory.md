# Agent 42: source-certified Machine C global rank and target-cutoff research

**Lease**: first claimed `2026-11-02T07:06:33Z`, run_id `98478f2b-f06b-4c8c-a338-56c5a1f619fb`. NEVER refresh the timestamp. At each checkpoint compute actual system clock elapsed; if at least 70min from original claim (08:16:33 UTC), finalize memory, push, delete lease as last mutation and verify.

## Progress through 07:24 UTC

**Verified, standard-axiom Lean 4.36.0-rc2 and successful manual unmodified-source CI [41405671155](https://github.com/FlareZ123/bb6/actions/runs/41405671155) at commit `5d14a2965e52c7372992feaefd7cd8260c8d542c`:**

- Original Machine C standalone exact acceleration from `im-results/agent11-c-line/CLine.lean`. Source semantics to original raw TM previously bridged by Agent21 CI 41389979481. Local copy of full nextC is definitionally equal to unmodified upstream, proven `source_next_agrees`.
- On all successful transitions weighted rank `R=a+2k+c` strictly increases, or stays constant while secondary `P=a+c` strictly falls. Every positive-length live execution is acyclic, from any source state, `source_no_positive_cycle`.
- On every all-equal-rank run n, `P(final)+n <=P(initial)`; any live `R(initial)+1`-step run must increase rank.
- Quantitative all-start all-target reachability cutoff: for *any* S,T, `(exists n, run n S = T) iff (exists n < (R(T)+1)^2, run n S = T)`. Formal `source_hit_target_iff_bounded`. Proof score `R*(B+1)+(B-P)`, monotone strictly under B-bounded successful edges, global <=(B+1)^2-1. For critical C thin target `(0,2j,4j+10)`, a fixed j has decision cutoff `(8j+11)^2` accelerated calls.
- Full Lean files in `im-results/agent42-c-no-cycles/{CNoCycles.lean,CNoCyclesBridge.lean,CBoundedRank.lean,CBoundedRankBridge.lean,README.md}`. Manual workflow `.github/workflows/agent42-c-no-cycles.yml` (dispatch only). Exact final CI passed with standard axioms and no sorryAx; no frontiers solved.
- Shared `communications/broadcast/2026-11-02T072239Z_agent42-c-quadratic-cutoff.md` notifies population.

**Critical scope:** The original Machine C and BB(6) remain undecided. The individual target bound is *not* a uniform bound over infinite halting target j. These findings belong in `im-results/`, not `results/`. Do not promote as publishable or novel.

## Need next

- Pursue a **uniform** infinite-index exclusion, a genuine forward invariant, or a new parametric symbolic inverse-tree closure. The current rank bound only turns fixed-index reachability into finite decidable problems.
- Source family `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, blank-entry (5,0,1), halting iff hit `(0,2j,4j+10)` for some j (Agent11 + Agent21 original bridge).
- Existing high-density inverse-residue proofs by Agent21/23/41, see `im-results/2026-11-02-cross-holdout-decision-gates-agent19.md`; avoid duplicating small isolated residues.
- B, P1, Sheep, Cryptid D-start remain active for other agents.
