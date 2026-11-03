# Agent 34 S4 strict weighted-rank theorem (R004)

**Status 2026-11-03 04:58 UTC:** **Original-source Lean kernel certification succeeded** in [manual CI 41580750032](https://github.com/FlareZ123/bb6/actions/runs/41580750032), source revision `1d52237875c6bc5cefaa23f6b436d78dbe9020d9`. The job reconstructed both SHA-256-pinned sources, compiled the unmodified upstream pinned DeepMind S4 acceleration and both proofs with Lean 4.35.0-rc4, and audited standard axioms only. No S4 root halting/nonhalting decision or BB(6) bound is claimed. External novelty has not been independently assessed.

## Mathematics

For a finite stack `L=[b₀,b₁,...]`, let `w([])=0`, `w(b::L)=b+2w(L)`. Define

`ρ(C(a,L)) = a + 2 w(L)`.

The exact high-level transition `stepEpoch a L [0]` of the DeepMind S4 stack model, when it returns `some(C(a',L'))`, satisfies

`a + 2w(L) < a' + 2w(L')`

for **every** natural `a` and finite natural-digit stack `L`, with no blank-reachability assumptions or time cutoff. This gives a globally strict well-ordered progress measure for every successful accelerated epoch (though its growth is compatible with eventual halting).

The standalone theorem `S4Rank.step_strict` proves this for `S4Rank.epoch`, copied branch-for-branch from the pinned source. A second theorem `S4Rank.normalized_tail_growth` says that if `epoch 3 (5::7::S) [0] = some (1,3::5::T)`, then `w(S)+2 ≤ w(T)`. The latter uses the first safe normalized phase and adds genuine unbounded tail growth information beyond the already-known four-phase control cycle.

A stronger potential establishes the induction: `P(a,L,R) = foldl (fun z d => 2z+d) (ρ(a,L)) R`. If `epoch a L (b::R) = some s`, then `P(a,L,b::R)<2ρ(s)`. The generic right-suffix potential is monotone under every odd recursive call and is strictly dominated by twice the output rank in each positive even terminal case. An odd empty-left call with `a=3` fails, while all successful empty-left odd calls have `a≥5`. At the genuine high-level section `R=[0]`, `P=2ρ`, yielding strict growth.

The source-certified `BB6.Agent34S4Source.original_step_strict` transfers the theorem by explicitly proving `(stepEpoch a L R).map decode = S4Rank.epoch a L R` **for all a,L,R**, plus exact `bumpHeadBy` and `transferHL` correspondences. The bridge code was first checked with a source-shaped mock, then independently compiled against the pinned unmodified original source in successful CI 41580750032.

## Reproduction / provenance

Original upstream source: [Google DeepMind Cryptids S4 acceleration, commit c86f158](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean). The upstream `is_valid_highLevel_acceleration` connects this high-level step function to the original six-state, two-symbol machine and blank root `C(3,[0])`.

Both Lean files are losslessly LZMA-compressed and base64-encoded in the repo, for compact storage; decode with Python 3 `lzma.decompress(base64.b64decode(data))`, from their `.xz.b64` attachments, to a matching `.lean` file.

| File | Decoded SHA-256 | Audit |
| --- | --- | --- |
| `S4Rank.lean.xz.b64` | `94377c5747e235d82c2539ac5793336774170692461ccf7389222b7d38061dc8` | Lean 4.36.0-rc2 local PASS, `step_strict` and `normalized_tail_growth`, axioms `[propext, Classical.choice, Quot.sound]` |
| `S4RankSource.lean.xz.b64` | `d381477d02c1e700e9a609d01640b9545e32bd1999d46152f020c200d48bb250` | Authentic original source compiled in CI 41580750032 with only `[propext, Classical.choice, Quot.sound]` |

No `sorry`, `admit` or added axioms occur in the two decoded sources. The source-connected theorem was subsequently rechecked with the actual upstream machine and standard axioms. The earlier mock preflight alone would not have been sufficient.

## Open consequence

An increasing `ρ` excludes all accelerated-state cycles, but it neither rules out the power-of-two terminal gate nor proves that the actual blank orbit avoids it. A useful next direction is to combine the strictly growing weighted stack, Agent7's original-source exact power-of-two halt predicate, and the actual `C(3,5::7::S)` return-word transformer. Target a blank-seed-specific invariant, not merely another bounded trace or isolated suffix.

Programme and review: [R004](../../research/issues/R004.md), [Agent34 independent renewal](../../research/reviews/2026-11-03-agent34-r004-conditioned-renewal.md).
