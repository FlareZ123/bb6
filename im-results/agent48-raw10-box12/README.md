# Raw10 base34 rectangle 12: complete weighted bound

**Mathematical status:** all completions of original-source `raw10Remainder[12]!` satisfy `WeightedBound 205`. On 28 November 2026, the exact generated `Box12Cover.lean` and corrected `Raw10RefinedBox12.lean` compiled locally with Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a), using all ten successful original-source branch objects and the exact common source bundle of [run 46112001673](https://github.com/FlareZ123/bb6/actions/runs/46112001673), plus the accepted original Box6 dependency artifact 15158192432. All twelve downloaded ZIP hashes are pinned in [recover-join.py](recover-join.py). The final original-source consumer audits exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, native oracle, or copied-machine replacement is used. This is a successful local composition of CI-compiled source, not a successful final hosted CI job or a new hosted final artifact.

The target code vector is [8,25,11,11,17,13,11,25,25,25,25,25], where 25 denotes a hole, 0 halt, and ordinary instructions are 1+4*state+2*write+right. E0 is restricted to [0,3,4,12,18,20,21,22,23,24]; the five other holes are unrestricted. Thus the bound applies to all **97,656,250** tables in this source rectangle. First-hole branching produces 5,982 splits and 143,554 leaves, including 65,548 left rays, 23,429 right rays, 21,371 cycles, 22,823 last-hole decisions, 5,982 halts and 4,401 initially open leaves. Bit FAR and sparse ngram extensions resolve 4,341 of the opens; the remaining 60 have checked block-FAR certificates (55 width-three, five width-two). The verified ordinary bound including the halt query is 200; the weighted target allows five initial blank-delay steps.

## Exact source interface

- `BB6.Agent48Box12.box12_weighted`: source-matched rectangle bound for every B≥205.
- `BB6.Agent48Raw10RefinedBox12.parentCover29`: gives the Raw10 Cover from the 29 explicitly retained refined rectangles at B≥7014.
- `BB6.Agent48Raw10RefinedBox12.parentCover27`: additionally requires the separate Box16 and Box17 weighted bounds, and 27 explicitly retained refined rectangles at B≥7376.

The last two theorems target the precise `BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC` definition. The older final job failed because the unqualified name resolved to `Agent50RootFrontier.firstOneB0_1LC`; the actual ten branch jobs and preparation succeeded. The corrected final consumer compiles without changing the branch source or objects. These counts describe this exact local predecessor; they do not establish a current global Canonical38 decrement, full Raw10 Cover, or BB(6) upper bound.

## Reproduce the accepted local join

Use [recover-join.py](recover-join.py) with Lean 4.36.0-rc2 and GitHub Actions artifact access:
```bash
python3 recover-join.py --artifact-dir /tmp/box12-zips --work /tmp/box12-recovered --out /tmp/box12-final
```
The script authenticates the twelve input archives, rejects duplicate branch modules, verifies the frozen join source, compiles only the two final modules, and rejects any missing or unexpected axiom profile. To use already downloaded archives, pass `--offline`. The existing [manual workflow](../../.github/workflows/agent48-raw10-box12.yml) has a join-only recovery input to create a durable final hosted artifact without re-running discovery or branch jobs.

Original generated join source SHA-256: `2358b8248f6cc44d205a3f2fda2764e224a35719fc85ab9fac296258a3622757`. Corrected consumer SHA-256: `51c7fc260d8f26afdf509440860b1e5e31e933a0c5b41f87609d7d182852e0c6`. The three exported theorems were audited locally on the exact original inputs. Original frozen run revision `c1a4058dbd45ba9aad3e943ddc110ef1182752b0`.

## Reusable source machinery

[PackedFinite.lean](PackedFinite.lean) proves packed natural-number tape encoding, exact finite and bounded simulation, packed translated-cycle soundness, halt/last-hole equivalence, and domain-restricted array-tree soundness. [Box12FourE0.lean](Box12FourE0.lean) is a historical four-branch intermediate; the complete ten-branch bound supersedes it. [Raw10RefinedBox12Cut.lean](Raw10RefinedBox12Cut.lean) proves the exact complement counts; [Raw10RefinedBox12.lean](Raw10RefinedBox12.lean) consumes the complete bound.
