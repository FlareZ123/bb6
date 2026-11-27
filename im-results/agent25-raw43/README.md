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

All 31 five-hole child specs across B1=1RC,0RC,0RA,1RA,1LB now have complete certificates. Bound candidates 382,620,390,519,289 respectively. Source accepted: full 1RC, 0RC and 0RA parents (45934715974,45937283185,45953249331). New 1RA and 1LB source gates not yet dispatched due to saturated runner queue. 1RA last two machines solved by period-12 block-DFA; 1LB last five machines solved by locally kernel-checked universal growth lemmas (`Raw43B1LBC0LAGrowth.lean`, `Raw43B1LBC1RAGrowth.lean`, `Raw43B1LBC1LEM103.lean`). See agent25 memory for exact run and dispatch details. `Raw43ParentCutExpandedFive.lean` is the candidate 23→5 canonical parent reduction at 1713; all outstanding child and composition acceptance must succeed before this reduction is a certified result. Other B1 branches with outstanding work include 0LE,1LA,1LE,1RE. The 0LA candidate is now complete (below). Manual `raw43-parent-reuse` mode `expandedfive` reuses successful artifacts with explicit pins and validates their exact source identities. No universal BB6 bound yet.

## B1=0LA: source-accepted parent bound 1771

Full eight-child parent composition: [45955232997](https://github.com/FlareZ123/bb6/actions/runs/45955232997), `BB6.Agent25Raw43B0LA.all_completions`. This closes all 25^6 raw completions.

`Raw43B0LACut.lean` is an eight-residual canonical cut at candidate weighted bound 1771; C1=0RC has a two-state FAR and the other side closures are cycles or E/F aliases. `Raw43B0LACompose.lean` connects the child bounds to the quotient and ordinary completion predicates. Both parent modules are source-accepted.

| C1 | Weighted bound | FAR | BiDFA | Late last | Late cycle | Growth | Source acceptance |
|---|---:|---:|---:|---:|---:|---:|---|
|0LA|337|86|28|2|0|0|[45940147007](https://github.com/FlareZ123/bb6/actions/runs/45940147007) success|
|0LB|129|94|128|0|0|0|[45953737515](https://github.com/FlareZ123/bb6/actions/runs/45953737515) success|
|0LE|172|408|105|0|1|0|[45953742298](https://github.com/FlareZ123/bb6/actions/runs/45953742298) success|
|0RE|235|445|28|1|0|0|[45953747932](https://github.com/FlareZ123/bb6/actions/runs/45953747932) success|
|1LA|113|226|38|0|0|0|[45953753821](https://github.com/FlareZ123/bb6/actions/runs/45953753821) success|
|1LB|195|204|104|0|6|0|[45953757431](https://github.com/FlareZ123/bb6/actions/runs/45953757431) success|
|1LE|158|666|92|0|1|0|[45953762245](https://github.com/FlareZ123/bb6/actions/runs/45953762245) success|
|1RE|1771|379|54|4|4|4|[45940958043](https://github.com/FlareZ123/bb6/actions/runs/45940958043) success|

All eight specs `spec_b0la_c*.json` have zero unresolved candidates. For 1RE, four difficult machines have constructive nonhalting invariants accepted together by source CI 45940958043. M234 returns from A([],0 1^(5n+13)) to A([],0 1^(5n+18)) in 22n+85 steps. M292 implements an unbounded digit-stack grammar with five-cell blocks. M195 and M200 share a sweep: A([1],00000001 (000001)^n T) returns to the same section with n+1 and terminal T toggled between empty and 01. The 26-step entry, 12-step right transfer, boundary turn (46/32 or 44/30), and 20/18-step left transfer and finish prove closure by positive-cost macro steps. See `Raw43B0LAC1REM{234,292,195200}.lean` for quantified arbitrary-tail equations and genuine blank-start bridges; these are included in the accepted 1RE child proof.

Earlier incarnations had local shell failures. The present toolchain is usable; original-source manual workflow remains available for exact acceptance checks. No new workflow. The exact source revision of the 1RE preflight is `55faa0285a87441cb72777ec1f615bf6868bb67f`.

## B1=1LA: A1 child banks

The canonical split has twelve nontrivial A1 child cylinders. Complete candidate banks and residuals:

| A1 | Weighted candidate threshold | Open leaves still unresolved | Source gate |
|---|---:|---:|---|
|0LA|4174|6|not closed|
|0LB|132|0|[45953260396](https://github.com/FlareZ123/bb6/actions/runs/45953260396) success|
|0LC|190|0|[45956808526](https://github.com/FlareZ123/bb6/actions/runs/45956808526) queued|
|0LD|127|0|[45956818528](https://github.com/FlareZ123/bb6/actions/runs/45956818528) queued|
|0LE|489|0|[45955470096](https://github.com/FlareZ123/bb6/actions/runs/45955470096) pending|
|0RC|126|0|[45956824286](https://github.com/FlareZ123/bb6/actions/runs/45956824286) queued|
|0RE|119|0|[45956829850](https://github.com/FlareZ123/bb6/actions/runs/45956829850) queued|
|1LB|325|0|[45954656171](https://github.com/FlareZ123/bb6/actions/runs/45954656171) success|
|1LC|52|0|[45956836451](https://github.com/FlareZ123/bb6/actions/runs/45956836451) queued|
|1LE|602|0|[45954501034](https://github.com/FlareZ123/bb6/actions/runs/45954501034) success|
|1RC|55|0|[45956842821](https://github.com/FlareZ123/bb6/actions/runs/45956842821) queued|
|1RE|134|0|[45954593167](https://github.com/FlareZ123/bb6/actions/runs/45954593167) success|

Candidate thresholds for unresolved children are not certified upper bounds. All twelve banks are persisted in `spec_b1la_a*.json`. Lag-XOR abstraction in `discover_abstract.js` transfers Agent19's compression to M147/M239 (1512 graph states; lag [8,3,2,2,1,1] both sides). A1=1LE M468 uses asymmetric rungram [3,2,2,3,1] vs width 8. M805 has six-one growth in 18n+27 steps from blank-entry B([],1^(6n+4)); M122 has three-pair growth in 36n+63 steps from A([], (01)^(3n+3)). Both growth proofs and M823's positive-cost ternary digit-stack invariant are source-accepted in CI 45954501034. M823 uses arbitrary-tail 2–4 step closure rules on A/D sections with right (001)^k111 and left a two-bit header followed by triple digits and an optional two-bit terminal.

Manual `raw43-b0la-compose` now uses the same exact source/manifest consumer as prior branches. All eight gates passed and the exact pinned parent composition succeeded. Local runtime unavailable; no new workflow introduced.

### Decider extensions for B1=1LA

- A1=1RE: M624/M625/M626 closed by asymmetric mod-five rungrams (95/420/433 abstract states); source accepted.
- A1=1LB: 24 unary-growth leaves closed by modulus 6 or 12 on the one-runs. The remaining E/F pair M25/M87 uses period-2/4 block compression, c=3,m=2,k=12, 1132 graph states. Source accepted.
- A1=0LE: 25 leaves closed by period-specific block summaries. M850–852 have common explicit ten-state FAR code `001239949596799895999` (left grammar bottom-up 11 then repetitions of 100, optional leading zero; absorbing invalid sink). M776 uses seven-state right FAR `101213433533623` (alternating prefix on unary ones, length mod 4). Arbitrary-width discovery checker in `discover_far_big.js`; original-source checker unchanged. Source gate pending.
- A1=0LA: asymmetric lag-XOR resolves M145/238,M155/247,M354/376. Aligned block-symbol rungram (new width/k/c/m in discover_abstract.js) resolves M156/248 at width 6,k=5,c=2,m=3 (17729 abstract states). Only M110/202,M151/243,M355/377 remain. Their mixed-period sweeps resist symmetric and asymmetric rungrams, period-block compression, lag-XOR, k-future trie folding and trace-restricted variants. These failures are not evidence of halting. The complete exact census and certificates are in spec_b1la_a0la.json.

## B1=1RE: E1 child banks

The E1=0LE child now has a complete candidate audit at weighted threshold 727. Its three hard leaves M55/M56/M57 differ only in F0, and share a ternary-counter induction in `Raw43B1REE0LEM555657.lean`. In left-includes-scanned notation, A carries a prefix of k digits as 3k+b ones, where b=0 or 2. Digits 000,100,010 encode 0,1,2. Digit 2 advances three live moves; digit 0 or 1 enters F, whose all-ones sweep rewrites the carried prefix as zero digits. The three distinct F0 boundary procedures take 1,17,23 moves. A reserved higher zero digit ensures that every carry terminates; induction on N proves a live prefix of length at least N from an explicitly padded blank tape. The padding embeds exactly to the physical blank configuration. Local Lean 4.36.0-rc2 checked `padded_live` and `never` using verbatim relevant semantic and transport excerpts of Frontier, RootShift, SparseZipper and SweepPumping, with axioms [propext, Quot.sound]. Full original import closure and exact child audit remain to be run; the threshold is not yet source-accepted.

| E1 | Weighted candidate threshold | Unresolved candidate leaves |
|---|---:|---|
|0LB|75|0 (M105 growth)|
|0LC|112|0 (M41 growth)|
|0LE|727|0 (three growth certificates, source accepted [45971431247](https://github.com/FlareZ123/bb6/actions/runs/45971431247))|
|1LC|684|0|
|1LD|85|0|

The E1-specific generator accepts explicit `b1re_e1*` names and uses slot 9, distinct from E0 slot 8. No full B1=1RE or Raw43 parent Cover is established.

### B1=1RE, E1=0LC: M41 binary-counter closure

M41 enters A0 after 27 transitions. Write P(n)=(10)^n 0100 (left list includes the scanned cell). A0(n) has left 00 P(2n+1) and empty right list; A1(j,R) has left P(2j+2), where R is any finite word of 1101/1111 digits ending in 110. Initialization costs 4n+24 and creates n one-digits. A zero-digit is removed at cost 4 with j incremented; a one-digit becomes a zero-digit after restoring j leading one-digits at cost 4j+20; the terminal word leads to A0(j+1) at cost 4. Every case preserves the invariant with positive cost. `Raw43B1REE1LCM41.lean` proves the completion-level `never` theorem (local Lean 4.36.0-rc2, axioms propext and Quot.sound, using the relevant source excerpts). The E1=0LC spec has no unresolved leaves; full source audit pending.

### B1=1RE, E1=0LB: M105 unary/alternating recycling

After 21 genuine blank-start transitions M105 enters A scanning zero, with left 0 1^7 and empty right list. More generally let B(k,R) have left 0 1^(8k+7). In 16k+58 transitions B(k,[]) returns to B(0,(10)^(4k+3)1). In 48k+74 transitions B(k,101U) returns to B(k+1,U.tail) whenever U.headD false=false. Restricting nonempty right words to (10)^(2j+1)1 makes this exactly closed: j=0 gives an empty word; otherwise j decrements. The proof uses arbitrary-length F/A sweeps (each exact macro checked, costs established by induction), then inducts over any number of returns. `Raw43B1REE1LBM105.lean` proves `never` for all compatible completions, locally checked under Lean 4.36.0-rc2 with propext and Quot.sound only against the relevant source excerpts. This removes the last unresolved leaf of the five prepared B1=1RE child specs, but source gates and exhaustive parent composition remain necessary.

### B1=1RE, further candidate banks

E1=0LA: threshold 223, 175 FAR + 60 BiDFA, zero gaps. E1=0RC: threshold 127, 243 FAR + 5 BiDFA + one growth. M174 has left grammar over 001,101,000,100 with terminator [] or 1, right (001)^k 01. The three-step carry removes 100 (or terminal 1); increment cases advance 001→101→000→100, reset k preceding zero digits; the empty word rebuilds them with a new terminal 1. Direct blank entry at step 23. `Raw43B1REE1RCM174.lean` gives locally checked arbitrary-length return, invariant and `never` (propext, Quot.sound). Both complete candidate banks still require original-source CI.


## 2026-11-27 late update: Raw43 candidate frontier is B1=0LE only

The strongest current candidate parent theorem is `Raw43ParentCutExpandedNine.lean`: after the already-developed branches B0LA, B1LA, B1LE and B1RE are composed with the earlier five-branch reduction, its residual list has length one and that residual is definitionally checked to be the B1=0LE parent. This is a candidate dependency reduction, not yet a source-accepted Raw43 cover.

For B1=0LE, `Raw43B0LEExpanded.lean` reduces the eight residual E0 cylinders of the accepted reduced cut to four: E0 in {1LA,1LB,1LF,1RF}. Finite-state abstraction then shrank the hard open frontiers from 246/180/861/42 leaves respectively to tiny structured sets. New exact closures include late last-hole hits at steps 1135,1211,2963,1569; a shift cycle for 1LA i31 at entry 25134 with period57; a permanent blank-left D0 ray for 1LB i746 after step1983; the source-certified M177 alternating-sweep recurrence; and a 6757-state asymmetric chunk BiDFA for the last M81 case in 1RF.

After these discoveries, the currently known genuinely long-lived recurrence frontier is six last-hole machines: 1LA i44/i62 and 1LF i330/i331/i396/i746, with source/integration work still required for the already-solved 1LB/1RF material. Deep abstraction outputs must be merged into the persistent child specs before claiming complete 1LA/1LB/1LF child theorems. No exact BB(6) value or universal six-state upper bound follows yet.
