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
| 0RC | C1 | 0LE,0RE,1LE,1RE | 620,239,546,94 | First two source accepted: 45934720356,45935729499; others running: 45936394408,45936493979 |
| 0RA | A1 | 0LE,0RC,0RE,1LB,1LE,1RE | 273,88,390,223,238,107 | Complete candidates; CI 45936971246,45936864320,45936975051,45936867896,45936979251,45936870974 |

The 0RC certificates include five new universal nonhalting machine proofs: digit-stack M2, paired alternating-block returns for 0RE, base-four counter M146, and alternating-block M155. Source files `Raw43B0RCC0LEM2.lean`, `Raw43B0RCC0REGrowth.lean`, `Raw43B0RCC1LEM146.lean`, `Raw43B0RCC1REM155.lean`. The 0RA candidates use 869 FAR, 297 BiDFA, 7 late halts and 9 late cycles; eleven hard leaves resolved with periodic-block BiDFA compression, including period-2 mod-3 cases. No additional residual candidate remains in these three branches.

For source-accepted children, use manual `agent10-four-hole.yml` targets `raw43-b1rc-compose`, `raw43-b0rc-compose`, `raw43-b0ra-compose` with `raw43_b1rc_pins` mapping child variants to successful run IDs. Exact Lean dependency manifests permit artifact reuse. Earlier 13-E1-child composition was interrupted by runner shutdown; no complete seven-hole parent claim yet.

### Expanded five-branch candidate bank

All 31 five-hole child specs across B1=1RC,0RC,0RA,1RA,1LB now have complete certificates. Bound candidates 382,620,390,519,289 respectively. Source accepted: full 1RC, all four 0RC children; 0RC parent gate 45937283185, 0RA gates listed above. New 1RA and 1LB source gates not yet dispatched due to saturated runner queue. 1RA last two machines solved by period-12 block-DFA; 1LB last five machines solved by locally kernel-checked universal growth lemmas (`Raw43B1LBC0LAGrowth.lean`, `Raw43B1LBC1RAGrowth.lean`, `Raw43B1LBC1LEM103.lean`). See agent25 memory for exact run and dispatch details. `Raw43ParentCutExpandedFive.lean` is the candidate 23→5 canonical parent reduction at 1713; all outstanding child and composition acceptance must succeed before this reduction is a certified result. Remaining B1 values 0LA,0LE,1LA,1LE,1RE. Manual `raw43-parent-reuse` mode `expandedfive` reuses successful artifacts with explicit pins and validates their exact source identities. No universal BB6 bound yet.
