# Agent 48 BB(6) research memory

## Invocation 2026-11-02

Normal research mode selected by actual cryptographic uniform draw **6** before any repo inspection. Claimed at **2026-11-02T10:07:08.922749Z**, run ID `agent48-gateway-56e200c0-f7c3-49ac-953f-921c9f3824eb`, lease `agents/agent48/.lease.json`. Never refresh. Mandatory time check after every checkpoint against this timestamp. Release only at **or after 2026-11-02T11:17:08.922749Z**, at a measured checkpoint, with lease deletion last after all useful state pushed.

## First formally verified Machine C finding

Source `im-results/agent48-c-middle-zero/KZeroMod4.lean` (imports actual Agent11 `CLine`) proves for all reachable `(a,0,c)` from accelerated blank entry `(5,0,1)`, the *exhaustive necessary shape*:

- `(5,0,1)`, or
- `(1,0,2*k+2)`, or
- `(4*k+5,0,d+4)`.

Hence `a%4=1`, `¬Reach(4*t+3,0,c)` and `¬Reach(a,0,0)` for all natural parameters. `reached_middle_zero_shape` has only axiom [propext], other theorems [propext, Quot.sound]. Direct local Lean 4.36.0-rc2 check passed and **original unmodified CLine CI successfully passed** [run 41427303952](https://github.com/FlareZ123/bb6/actions/runs/41427303952). The proof is strictly stronger than Agent21's `CBack.reached_kzero_odd` (a odd only), but no new C reset family excluded yet. Need assess substantive impact before any `results/` promotion. Full evidence and limitations in `im-results/agent48-c-middle-zero/README.md`; broadcast `communications/broadcast/2026-11-02T1017Z_agent48-c-kzero-mod4.md`.

Repo README prohibits workflows automatically triggered on commits. Our `.github/workflows/agent48-c-middle-zero.yml` is manual workflow_dispatch only.

## Existing state of research

Public result source `results/README.md` mainly catalogs source-certified Machine C infinite congruence classes. Other major undecided holdouts: P1, B, C, Sheep, Cryptid D-start. Cross-holdout synthesis `im-results/2026-11-02-cross-holdout-decision-gates-agent19.md` gives exact halting criteria for four. P1 inverse families heavily pursued by Agents4/28/33/50. C inverse/quotients heavily pursued by Agents21/29/34/41. Cryptid source symbolic code pursued by Agents25/26/31/32/35/37. Avoid recreating overlapping work.

Relevant Machine C helpers: `im-results/agent21-c-source-bridge/{CRange,CBack,CHubSplit}.lean`, `im-results/agent29-c-inverse` and `im-results/agent41-c-quotient512` computational systems. Next priority: integrate new k=0 shape to search for genuinely new inverse exclusions outside prior quotient, or switch to more promising underexplored family if no gain.

Local Lean toolchain assembled from user-uploaded split archive at `/tmp/lean/lean-4.36.0-rc2-linux/bin/lean`; local scratch `/tmp/agent48/CLine.lean` (minimal exact relevant source declarations) and `/tmp/agent48/KZeroMod4.lean`. Those paths are ephemeral; original source in GitHub. CI checks real CLine. No exact BB(6) value or global upper bound established.
