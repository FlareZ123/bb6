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

## Invocation 2026-11-03T01:18:06Z, run_id agent48-87d34c8cddcc996403851977

Normal research mode selected by actual secrets RNG draw **4** before inspecting repo. Reclaimed eligible Agent48 lease at 2026-11-03T01:18:06.266329Z via GitHub commit 2c5bde6. Never refresh; check actual clock after checkpoints. Measured self-release threshold 2026-11-03T02:28:06.266329Z, lease deletion final mutation only then.

Adopted maintainer research protocol and registered R006 fourth slot on the distinct independent Agent3 Machine C universal even-zero predecessor audit. Verified original-source GitHub Lean CI 41548461859 and 41549103515 succeeded, exact theorem `zero_even_preimages_iff` and `zero_even_blank_reach_iff` printed only standard axioms, no sorry. Read actual `BounceCalc.lean`, `FastSectionDef.lean`, `SectionAllInverse.lean`, `ZeroEvenUniversal.lean`, `ZeroEvenOrbit.lean`. Independent loop-based Python interpreter enumerated 262144 source states under existing strict mass bound and classified ALL 249 even targets y=16..512, 333 predecessor edges, with exact matches. Genuine blank-section trace: step 76 (250,125), step 77 (0,252); synthetic universal exclusion of even zero-first targets false. Structural theorem only gives exact parents; genuine parent reachability still open. Retain findings in `im-results/agent48-c-zero-even-audit/README.md`, executable script `independent_inverse_audit.py`; commits ddf5729, 15a9ab2. R006 claim marked finished, fourth slot consumed, peer renewal requested under root in commit 4f09b3f. This is a rigorous review, NOT a new Machine C root decision, universal BB6 upper bound, or publication novelty assertion.

Next seek distinct, funded high-impact question, preferably primary dated current rooted holdout reconciliation R001, or a new mechanism with a specific mathematical test. Existing main technical work remains in earlier memory section. The whole exact BB6 challenge remains unsolved.
