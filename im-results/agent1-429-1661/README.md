# BB(6) holdout #429: two new genuine blank-root terminal exclusions modulo 2048

Agent 1, 2026-11-04. **Original-repository accelerated-source Lean proof succeeded for both infinite classes. **The separate pinned original DeepMind Cryptids raw-source transport PASSED full original-source CI [41873655005](https://github.com/FlareZ123/bb6/actions/runs/41873655005), completed 2026-11-04 17:12:38 UTC.** This verifies both exact source transport lemmas and the native raw `IsHalt` equivalence to the 86 surviving mod2048 gate filter, with only standard axioms and no `sorry`.** This is an intermediate structural result about one unresolved six-state machine. It does **not** prove machine #429 nonhalting or determine BB(6).

## Exact all-time theorems

The accelerated root `BB429.run n (0,0)` uses the unchanged machine-specific `BB429.next` from [Agent 5's source](../agent5-429-rank/BB429Rank.lean). Its only halting line is `b+1=2*a`. Our two entirely quantified theorems prove:

```lean
BB429No1661mod2048.blank_halt_not_1661_mod2048 :
  ∀ n a b, BB429.run n (0,0) = some (a,b) →
    b+1=2*a → a%2048≠1661

BB429No893mod2048.blank_halt_not_893_mod2048 :
  ∀ n a b, BB429.run n (0,0) = some (a,b) →
    b+1=2*a → a%2048≠893
```

Both modules passed unchanged **local repository-source** Lean v4.36.0-rc2 in the [source-integrated manual CI run 41873463983](https://github.com/FlareZ123/bb6/actions/runs/41873463983). The first was separately checked in [41872637994](https://github.com/FlareZ123/bb6/actions/runs/41872637994). Each compiled without `sorry` or `native_decide`; the printed kernel theorem dependency set contains only standard `[propext, Classical.choice, Quot.sound]`. The first attempt 41872401822 had a base64 transport artifact error and was repaired before either successful kernel check.

The two exclusions are disjoint modulo 2048 and belong to different classes `a%1024=637` and `a%1024=893`, both expressly reported as surviving in [Agent 6's 2026-11-04 16:44 broadcast](../../communications/broadcast/20261104T1644Z_agent6-four-mod1024-halting-gates.md). They do not duplicate Agent6's already eliminated `125,381,509 (mod1024)` or Agent18's `253 (mod1024)`. Internal historical overlap must still be audited; no external novelty claim has been established.

## How the 1661 family is excluded

For a hypothetical reached halting state `a=2048q+1661`, the unique source-valid immediate halting-line predecessor is `(1024q+829,6144q+4982)`. Four exact forced first-only inverse steps lead to `S=(64q+49,8064q+6530)`.

A complete `next` case split proves `S` has only two possible predecessors:

- `A=(32q+23,8128q+6579)`. Its unique rooted predecessor is `(16q+10,8160q+6602)`. If `q=0`, this is `(10,6602)`, excluded for all time by the exact blank checkpoints `run 1443=(3069,476)` rank 6614 and `run 1444=(0,6624)` rank 6624, with the strict rank increase at every surviving step. If `q>0`, two further forced inverse steps yield a positive even first coordinate with an odd second coordinate, contradicting `rooted_even_parity`.
- `B=(2080q+1675,4032q+3267)`. Its forced parent is `(1040q+836,6112q+4942)), whose unique incoming source parent is `(2568q+2068,3056q+2471)`. This has positive even first coordinate and second counter congruent to three modulo four, contradicting the same root invariant.

All predecessor exhaustiveness is proved by exact case splits on the original `BB429.next`, with no finite inverse cutoff. The specialized `q=0` blank trace is kernel checked by `decide` and bounded-rank propagation.

## How the 893 family is excluded

For hypothetical `a=2048q+893`, its unique halting-line predecessor is `(1024q+445,6144q+2678)`. Four forced inverse steps lead to `S=(64q+25,8064q+3506)`, whose complete predecessor split gives:

- `A=(32q+11,8128q+3531)`. For `q=0` its only parent is `(4,3542)`, and a separate complete source case split proves **no input whatsoever has first counter output 4**, so this is impossible at positive root time. For `q>0`, one more exact predecessor forces a positive even counter whose parent has right coordinate three modulo four, forbidden on the actual blank orbit.
- `B=(2080q+895,4032q+1755)`. A forced first-edge and then an exact even-output inverse reduce rooted reachability to `(2568q+1105,3056q+1325)`. Its two further forced odd predecessors produce positive even first counter with second counter one modulo four, again impossible.

Here the new universal no-parent-of-first-counter-4 lemma replaces an expensive long exact root checkpoint at the small parameter boundary.

## Consequence for genuine raw machine halting

The previously source-certified [Agent 6 44/1024 condition](../agent6-harmonic429/SourceRawHalt44.lean) is equivalent to a filter with **88** candidate classes modulo 2048. Removing the two distinct new classes leaves **86/2048** necessary candidate terminal residues. The explicit new theorem [`SourceRawHalt86.lean`](SourceRawHalt86.lean) imports the previous actual source bridge and both new independent root exclusions to assert the exact original-source halting **iff** reachability of one of these remaining filtered terminal states. Native upstream Lean4.35 original Cryptids source compilation **succeeded** at [run 41873655005](https://github.com/FlareZ123/bb6/actions/runs/41873655005); [workflow](../../.github/workflows/agent1-429-native-86.yml) pins upstream SHA `c86f15861709b76042998c5211c7b2f83991621b`.

Neither the 86 candidates nor a particular one is known blank-reachable. Thus the exact #429 halting decision, a BB(6) upper bound and BB(6)'s exact value remain open.

## Reproduction

- The 1661 module `BB429No1661mod2048.lean` is archived in [gzip base64](BB429No1661mod2048.lean.gz.b64), uncompressed SHA256 `05576abaf58d8b62f97e2390b017bc1e5086693512339fc6abdb3f386c6a9793`.
- The 893 module `BB429No893mod2048.lean` is archived in [gzip base64](../agent1-429-893/BB429No893mod2048.lean.gz.b64), uncompressed SHA256 `7429ab3280d28d13f5e21702523ed750c9a2e61679ff10e9e9108534b5984b32`.
- The [manual accelerated-source CI](../../.github/workflows/agent1-429-1661.yml) decodes both proof files and checks their SHA256 hashes before compiling exact unchanged source dependencies. [Native-source CI](../../.github/workflows/agent1-429-native-86.yml) also checks the upstream Cryptids module and full raw halting bridge.
- Existing comprehensive source proof dependencies are [Agent 6's rooted parity](../agent6-harmonic429/BB429LowOddMod8.lean), [Agent 6's source predecessor helper](../agent6-harmonic429/BB429No381mod1024.lean) and [Agent 5's BB429 rank code](../agent5-429-rank/BB429Rank.lean).

## Next mathematical targets

Try to eliminate the complementary `a%2048=637` and `a%2048=1917` subclasses and then the whole `637 (mod1024)` and `893 (mod1024)` sectors, while checking in-progress work by Agents 6/18. The forward blank reset restrictions, including all genuine non-first seeds and first-branch burst lengths, are more useful toward full nonhalting than repeated refinement of small disconnected cylinders.

## Native source verification update (17:12 UTC)

[Successful exact original-pinned-source Lean CI 41873655005](https://github.com/FlareZ123/bb6/actions/runs/41873655005) compiled unchanged upstream Cryptids source at SHA `c86f15861709b76042998c5211c7b2f83991621b`, all unchanged local source dependencies, the two independently checksum-checked new source modules, and `SourceRawHalt86.lean`. Therefore the source-level 86/2048 halting iff criterion is fully proved. Keep this in `im-results` because external mathematical novelty and independent priority remain unreviewed; it is not a halting decision for #429 or BB(6).
