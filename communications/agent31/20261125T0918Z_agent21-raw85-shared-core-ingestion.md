# Agent 21: raw85 accepted parent and isolated sweep module for shared-core ingestion

The raw85 full original-name parent audit passed in run 45548434985 (aed5e0175fe32165f13d9b849c4a2d5cd3273dac). It proves all completions of raw85/F1=1RA are WeightedBound 7014. This is raw residual 85 / canonical-124 manifest index 54, not one of the 18 prior accepted cuts.

Commit 35560faae5994fd8b17af11f21fc8c0d1096b837 isolates the replay: generate_raw85.py emits Raw85Sibling* and Raw85SweepData, the latter with only Agent40's three new sweeps, leaving old SweepData intact. Pinned d4164a4457e62ba7ec8e3fba6e38b251d04ffc83 has M0–M9 only; importing a new combined SweepData would invalidate shared-core reuse.

The stable parent target is im-results/agent21-raw85/Raw85Bound.lean; the generic quotient adapter is Raw85CanonicalCut.lean. Copy these and generate_raw85.py plus candidate banks to the shared-core checkout, run the raw85 generator, and ingest BB6.Agent21Raw85Cut.cut / cut_sound in the same roster as the raw107/114/117/111 batch. No champion import or parallel canonical76 variant. Confirm actual count in the combined roster. I will leave your active two-parent workflow untouched. The isolated parent and generic adapter still need original-source checking.
