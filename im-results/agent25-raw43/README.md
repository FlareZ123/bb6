# Raw43: canonical parent cut and five-hole child bounds

Parent: `1RB---_1RC---_0RD---_1LD0RB_------_------` (seven holes). First missing transition B1; E/F renaming preserves the parent and blank start.

## Source-accepted progress

| E1, with B1=0RE | Weighted bound | Side cycles | Last holes | Split nodes | Additional certificates | CI |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| 0LE | 75 | 5371 | 995 | 279 | 51 FAR + 1 growth | [45806858894](https://github.com/FlareZ123/bb6/actions/runs/45806858894) |
| 0RD | 49 | 2878 | 273 | 137 | 1 FAR | [45921443774](https://github.com/FlareZ123/bb6/actions/runs/45921443774) |
| 1RD | 1713 | 4203 | 641 | 212 | 25 FAR + 1 late last + 7 growth | [45922723471](https://github.com/FlareZ123/bb6/actions/runs/45922723471) |

Each child covers all 25^5 = 9,765,625 raw completions. WeightedBound includes first-one delay. Source theorem names respectively `BB6.Agent25Raw43.all43child`, `BB6.Agent25Raw43RD.all43child`, `BB6.Agent25Raw43RD1.all43child`.

`Raw43ParentCut.lean` gives a source-accepted conditional reduction of Raw43 to 21 canonical residuals instead of the 23 from the initial two-level cut. It absorbs 0LE and 0RD, not yet 1RD. See [45922648873](https://github.com/FlareZ123/bb6/actions/runs/45922648873), exact theorem `BB6.Agent25Raw43Parent.cover`. **Raw43 remains open**; this is not a canonical roster deletion.

## Universal growth

- 0LE M29: `1RB0RF_1RC0RE_0RD0RA_1LD0RB_1LF0LE_1LB---`. In left-includes-scanned zipper notation, S(n) = (A,[1,0,1],(01)^n 0). Entry S(1) after 16; S(n) → S(n+3) in 8n+28 steps.
- 1RD: `Raw43RD1Growth.lean` establishes shared E-state sweeps. `Raw43RD1Return.lean` resolves five variants of the C1 instruction; return from A([], (01)^m) to A([], (01)^f(m)) with f(m)=2m+3, 3 ceil(m/2)+3, or 3 floor(m/2)+3. `Raw43RD1M0.lean` gives linear alternating-block growth. `Raw43RD1M29.lean` proves a little-endian binary counter invariant covering both missing entries A1/C1.
- 0RD M0: `1RB0LF_1RC0RE_0RD---_1LD0RB_1RF0RD_1LA0RE`; one-state FAR orientation 0, delta [0,0], left masks [2,4,8,26,32,16,64], right masks [32,16,64,2,8,16,64], blank-zero closure mask 64.

## Active candidate siblings

| E1 | Weighted candidate bound | FAR | Other certificates / gaps |
| --- | ---: | ---: | --- |
| 0RE | 41 | 122 | complete candidate |
| 1RE | 128 | 177 | 2 growth drafts |
| 0RF | 144 | 138 | 5 unresolved |
| 1LB | 115 | 159 | 5 unresolved |

The exact open roster, split census and FAR candidates are in `spec_*.json`. `discover.js` uses 32-bit rolling hashes only for candidate selection and exact versioned-tape comparison; it is not a trusted proof checker. `generate.py` independently uses the C++ enumerator and emits Lean exact certificates. Existing workflow agent10-four-hole.yml supports raw43-child, raw43-0rd, raw43-1rd, raw43-parent-cut, and raw43-extra (raw43_extra_child=0re or 1re etc). Local shell and Python returned ClientError before execution; original-source CI is the compilation route. No unverified candidate is promoted to a certified bound.

## 2026-11-27 branch closure

**B1=1RC is source-accepted in full**, weighted bound 382: [CI 45934715974](https://github.com/FlareZ123/bb6/actions/runs/45934715974), `BB6.Agent25Raw43B1RC.all_completions` and `.cover`. The canonical cut checks six residuals and the child proof artifacts independently establish their bounds. This classifies 25^6 physical completions (244,140,625).

| B1 | Child slot | Child variants | Weighted bounds | Status at checkpoint |
|---|---|---|---|---|
| 1RC | C1 | 0LA,0LE,0RE,1LA,1LE,1RE | 118,112,105,75,96,382 | Full parent accepted |
| 0RC | C1 | 0LE,0RE,1LE,1RE | 620,239,546,94 | Full parent source accepted: [45937283185](https://github.com/FlareZ123/bb6/actions/runs/45937283185) |
| 0RA | A1 | 0LE,0RC,0RE,1LB,1LE,1RE | 273,88,390,223,238,107 | Full parent source accepted: [45953249331](https://github.com/FlareZ123/bb6/actions/runs/45953249331); artifact 15178155550 |

The 0RC certificates include five new universal nonhalting machine proofs: digit-stack M2, paired alternating-block returns for 0RE, base-four counter M146, and alternating-block M155. Source files `Raw43B0RCC0LEM2.lean`, `Raw43B0RCC0REGrowth.lean`, `Raw43B0RCC1LEM146.lean`, `Raw43B0RCC1REM155.lean`. The 0RA candidates use 869 FAR, 297 BiDFA, 7 late halts and 9 late cycles; eleven hard leaves resolved with periodic-block BiDFA compression, including period-2 mod-3 cases. No additional residual candidate remains in these three branches.

For source-accepted children, use manual `agent10-four-hole.yml` targets `raw43-b1rc-compose`, `raw43-b0rc-compose`, `raw43-b0ra-compose` with `raw43_b1rc_pins` mapping child variants to successful run IDs. Exact Lean dependency manifests permit artifact reuse. Earlier 13-E1-child composition was interrupted by runner shutdown; no complete seven-hole parent claim yet.

### Expanded five-branch candidate bank

All 31 five-hole child specs across B1=1RC,0RC,0RA,1RA,1LB now have complete certificates. Bound candidates 382,620,390,519,289 respectively. Source accepted: full 1RC, 0RC and 0RA parents (45934715974,45937283185,45953249331). New 1RA and 1LB source gates not yet dispatched due to saturated runner queue. 1RA last two machines solved by period-12 block-DFA; 1LB last five machines solved by locally kernel-checked universal growth lemmas (`Raw43B1LBC0LAGrowth.lean`, `Raw43B1LBC1RAGrowth.lean`, `Raw43B1LBC1LEM103.lean`). See agent25 memory for exact run and dispatch details. `Raw43ParentCutExpandedFive.lean` is the candidate 23→5 canonical parent reduction at 1713; all outstanding child and composition acceptance must succeed before this reduction is a certified result. Other B1 branches with outstanding work include 0LA,0LE,1LA,1LE,1RE. The 0LA candidate is now complete (below). Manual `raw43-parent-reuse` mode `expandedfive` reuses successful artifacts with explicit pins and validates their exact source identities. No universal BB6 bound yet.

## B1=0LA: complete candidate branch

`Raw43B0LACut.lean` is an eight-residual canonical cut at candidate weighted bound 1771; C1=0RC has a two-state FAR and the other side closures are cycles or E/F aliases. `Raw43B0LACompose.lean` connects the child bounds to the quotient and ordinary completion predicates. Both parent modules still require original-source acceptance.

| C1 | Weighted bound | FAR | BiDFA | Late last | Late cycle | Growth | Source acceptance |
|---|---:|---:|---:|---:|---:|---:|---|
|0LA|337|86|28|2|0|0|[45940147007](https://github.com/FlareZ123/bb6/actions/runs/45940147007) success|
|0LB|129|94|128|0|0|0|[45953737515](https://github.com/FlareZ123/bb6/actions/runs/45953737515) dispatched|
|0LE|172|408|105|0|1|0|[45953742298](https://github.com/FlareZ123/bb6/actions/runs/45953742298) dispatched|
|0RE|235|445|28|1|0|0|[45953747932](https://github.com/FlareZ123/bb6/actions/runs/45953747932) dispatched|
|1LA|113|226|38|0|0|0|[45953753821](https://github.com/FlareZ123/bb6/actions/runs/45953753821) dispatched|
|1LB|195|204|104|0|6|0|[45953757431](https://github.com/FlareZ123/bb6/actions/runs/45953757431) dispatched|
|1LE|158|666|92|0|1|0|[45953762245](https://github.com/FlareZ123/bb6/actions/runs/45953762245) dispatched|
|1RE|1771|379|54|4|4|4|[45940958043](https://github.com/FlareZ123/bb6/actions/runs/45940958043) success|

All eight specs `spec_b0la_c*.json` have zero unresolved candidates. For 1RE, four difficult machines have constructive nonhalting invariants accepted together by source CI 45940958043. M234 returns from A([],0 1^(5n+13)) to A([],0 1^(5n+18)) in 22n+85 steps. M292 implements an unbounded digit-stack grammar with five-cell blocks. M195 and M200 share a sweep: A([1],00000001 (000001)^n T) returns to the same section with n+1 and terminal T toggled between empty and 01. The 26-step entry, 12-step right transfer, boundary turn (46/32 or 44/30), and 20/18-step left transfer and finish prove closure by positive-cost macro steps. See `Raw43B0LAC1REM{234,292,195200}.lean` for quantified arbitrary-tail equations and genuine blank-start bridges; these are included in the accepted 1RE child proof.

Local shell and Python remain unavailable in this invocation (ClientError/TooManyActiveSessionsError before commands). Original-source manual workflow is used for selective acceptance checks; no new workflow. The exact source revision of the 1RE preflight is `55faa0285a87441cb72777ec1f615bf6868bb67f`.

## B1=1LA: A1 child banks

The canonical split has twelve nontrivial A1 child cylinders. Complete candidate banks and residuals:

| A1 | Weighted candidate threshold | Open leaves still unresolved | Source gate |
|---|---:|---:|---|
|0LA|4174|14|not closed|
|0LB|132|0|[45953260396](https://github.com/FlareZ123/bb6/actions/runs/45953260396) success|
|0LC|190|0|candidate|
|0LD|127|0|candidate|
|0LE|489|29|not closed|
|0RC|126|0|candidate|
|0RE|119|0|candidate|
|1LB|325|26|not closed|
|1LC|52|0|candidate|
|1LE|602|1|two growth drafts pending source check|
|1RC|55|0|candidate|
|1RE|134|3|not closed|

Candidate thresholds for unresolved children are not certified upper bounds. All twelve banks are persisted in `spec_b1la_a*.json`. Lag-XOR abstraction in `discover_abstract.js` transfers Agent19's compression to M147/M239 (1512 graph states; lag [8,3,2,2,1,1] both sides). A1=1LE M468 uses asymmetric rungram [3,2,2,3,1] vs width 8. M805 has six-one growth in 18n+27 steps from blank-entry B([],1^(6n+4)); M122 has three-pair growth in 36n+63 steps from A([], (01)^(3n+3)). Their Lean sources are drafts until CI passes.

Manual `raw43-b0la-compose` now uses the same exact source/manifest consumer as prior branches. Once all eight child gates pass, supply explicit C1 run pins. Local runtime unavailable; no new workflow introduced.
