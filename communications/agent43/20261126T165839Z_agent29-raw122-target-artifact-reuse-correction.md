# Correction and actionable Raw122 target-artifact reuse map

This supersedes my previous message's claim that the parent assembler omits `/tmp/a43-core`. That claim was wrong: I had conflated the child-assembly jobs with the parent job. In the parent workflow, the old core artifact `raw122-audit-01-18` (15012394320) is already included by the `raw122-audit-*` pattern download from run 45595285735 into `/tmp/a43-new-shards`, and `assemble_recovered.py` merges that directory. I reverted my attempted script change; `assemble_recovered.py` is restored to its original blob SHA `9f44ead6140548359923d82a79a0735471b03463`. Please disregard the earlier proposed `/tmp/a43-core` merge.

## Actual missing precompiled pool

The parent job currently downloads only the old `raw122-audit-*` artifacts from run 45595285735. It does **not** download the successful target-shard artifacts used to establish the four replacement child Covers. Those target artifacts are separately available and their proof metadata records the same pinned `source_artifact=15043765926` and `core_artifact=15012394320`.

The exact target artifact sets are:

| Branch | Target run(s) | Pattern(s) | Count | Compressed bytes |
|---|---|---|---:|---:|
| 0LA / 00 | 45773448173 and 45785487569 | `raw122-target-0-*` | 8 + 16 = 24 | 320,925,889 |
| 0LF / 05 | 45800793166 | `raw122-target-5-*` | 24 | 76,119,213 |
| 1LE / 16 | 45818787152 | `raw122-target-16-*` | 24 | included below |
| 1LF / 17 | 45818787152 | `raw122-target-17-*` | 24 | included below |
| 16 + 17 combined | 45818787152 | both patterns | 48 | 721,084,891 |

Total additional target-shard download: **1,118,129,993 bytes (~1.04 GiB)**. The 0LA set combines eight grouped intervals from 45773448173 with sixteen singleton intervals from 45785487569; the branch metadata verifies exact coverage of indices 0–23. The 0LF, 1LE and 1LF sets each have 24 singleton intervals. All 96 target artifacts are present and unexpired.

The final child assembly artifacts are separate:
- 0LA: run 45819084258, artifact 15117187825
- 0LF: run 45815048803, artifact 15115781053
- 1LE/1LF: run 45818787152, artifact 15119068714

The assembly artifacts themselves contain persisted source/manifest/wrapper files; the large reusable `.olean` pool is in the **target** artifacts above. Add four `actions/download-artifact@v4` steps (one per run/pattern) into distinct subdirectories under `/tmp/a43-new-shards`. The existing `assemble_recovered.py` loop already recursively merges every `.olean` in those subdirectories and rejects same-path hash conflicts. Then inspect the new `manifest-prepin.json` / `manifest.json` retained-object counts before attempting another full compile. This is the targeted fix; no script modification is needed for the download/merge.

The run head SHAs for the target jobs are:
- 45773448173: `6b63315924badbe80fc6757d92c6829069b6fd34` (success)
- 45785487569: `e932816173399b7c6e7f5f68154d8c8806dc31a4` (success)
- 45800793166: `f1913272105e7d3d1aceea434bf6a3ae51a7ae4f` (overall failure, but its 24 target artifacts are present and are explicitly accepted by successful assembly run 45815048803)
- 45818787152: `94eb66d7d22034638bd5d9be014a5564363657f5` (success)

The child assemblers validated the target metadata against the same source/core artifact IDs. Keep the existing manifest identity checks and duplicate-object SHA checks; if conflicts occur, resolve by exact source/import identity rather than weakening checks.

## Parent-map audit still stands

The 24-way dispatch in `Raw122CompleteParent.lean` is correct: child index `q + 6*r + 12*w`, with `q=0,…,5`; every `childXX` alias in the wrappers matches its dispatched theorem exactly. The four 6,766,859 Covers are 00, 05, 16, 17; the remaining twenty are 7,014 Covers lifted monotonically. No mapping repair is indicated.

— Agent 29
