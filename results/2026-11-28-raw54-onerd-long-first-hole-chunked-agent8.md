# Long Raw54 E1=1RD first-hole certificates by kernel-checked zipper chunking

**Result (28 November 2026).** Three disjoint one-hole cylinders in the Raw54 `E1=1RD` family have exact verified first-unassigned-transition times **69,753** or **87,079** on the initially blank tape. For every ordinary completion of each cylinder, the original-source Lean theorem establishes `WeightedBound 100000`; together they cover **75** ordinary complete machines. Their original-source Lean 4.36.0-rc2 `Cover` proofs were independently **accepted in all three jobs** of [CI 46155829562](https://github.com/FlareZ123/bb6/actions/runs/46155829562), with `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Additionally, for each one-hole table, the locally source-checked `witness_halts` theorem constructs its halting completion and proves `HaltsAfter witness n` at the exact displayed first-query step. These strengthened witness theorems are included in a second CI replay of the generator.

## Precise machines and first-hole times

All transitions are from states A through F, reading 0 and 1 respectively. `---` is the **single** unassigned instruction F0, so every specified partial table has 25 ordinary completions (halt or one of 24 ordinary nonhalting instructions).

| Literal partial machine | Blank steps before F0 first queried | Cover bound |
| --- | ---: | ---: |
| `1RB1RF_1RC0RA_0RD1RB_1LD0LE_1LA1RD_---1RC` | **69,753** | 100,000 |
| `1RB0RF_1RC0RA_0RD1RB_1LD0LE_1LA1RD_---0LA` | **87,079** | 100,000 |
| `1RB1RF_1RC0RA_0RD1RB_1LD0LE_1LA1RD_---0LC` | **87,079** | 100,000 |

At each claimed time, the original execution has completed that many defined primitive transitions without requesting any unassigned instruction; the next transition request is exactly F0. All other entries are assigned nonhalting transitions. For a halting F0 fill this yields a finite terminating run; for any other fill all transitions are nonhalting. The `Cover (WeightedBound 100000)` theorem treats both possibilities uniformly, including the weighted first-one normalization.

## Exact source proof mechanism

The main result is not a claim that the untrusted Python simulation determines a first-hole query. The simulation merely emits finite zipper *snapshots*, and Lean checks **every edge independently** against the original six-state partial table before deriving a theorem.

1. Fix the literal `PartialMachine p`, `Z` zipper semantics, and `start = ⟨0,0,[],[]⟩`. At times 1,000, 2,000, … and finally the given query step, emit explicit zipper configurations `cfgᵢ : Z`. Repeated tape symbols are encoded compactly with `List.replicate`.
2. For every adjacent pair prove by trusted kernel computation `segmentᵢ : zrun p (tᵢ-tᵢ₋₁) cfgᵢ₋₁ = some cfgᵢ`; `cfg₀ = start`. Each segment has at most 1,000 defined primitive transitions, avoiding the memory blowup of deciding a giant `zrun` all at once.
3. Obtain each `prefixᵢ : zrun p tᵢ start = some cfgᵢ` by repeated application of the previously source-proved general `BB6Coverage.Agent50Zipper.join` (which itself uses `zrun_add`). The final `prefix70` (69,753 case) or `prefix88` (87,079 cases) is a fully kernel-checked original-execution equality. The prefix theorems depend only on `propext` and `Quot.sound`.
4. Rewrite original-source `zipRead p tᵢ` using the exact `prefixᵢ`, decide that it reads F0, and check `restOK p (5,false)`, `weightedTNFNoAssignedHalt p`, and the anchored `initialSlot = 1RB`. The combined `zipCheck 100000 p (.last n (5,false)) = true` produces `Cover (WeightedBound 100000) p` through original-source `certifiedZip` soundness.

The resulting three `cover` theorems were accepted by original-source GitHub CI, with the standard Lean axiom profile `[propext, Classical.choice, Quot.sound]`, no private axiom, `sorry`, or trust in generated snapshots. Three corresponding `witness_halts` proofs locally checked the exact halting instructions with the same standard axiom profile. The machine-code generator is [generate_onerd_zipchunk.py](../im-results/agent8-raw54/generate_onerd_zipchunk.py), and [the original-source CI workflow](../.github/workflows/agent8-raw54-onerd-zipchunk.yml) regenerates each complete Lean source file and audits these exports.

## Scope and next integration

The three partial machines form distinct one-hole cylinders in the original Raw54 1RD residual search. This result **does not** cover the full Raw54 `E1=1RD` child or any of the canonical global BB(6) holdouts without further composition. It complements the [625-completion two-hole growing-run nonhalting theorem](2026-11-28-raw54-onerd-twohole-growth-agent8.md) and the separate (source-checked individual) 445-certificate FAR portfolio in [the working research ledger](../im-results/agent8-raw54/README.md).

The important transferable technique is proof-carrying *long finite execution*: an arbitrarily long known partial run can be verified by a sequence of small exact local reductions and composed with the original semantic `zrun_add` theorem, avoiding monolithic recursive kernel reduction. This is especially useful for BB(6) late-hole families where 70,000–90,000 primitive transitions would otherwise exceed a single Lean process's working-memory budget.
