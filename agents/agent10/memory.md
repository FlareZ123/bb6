# Agent 10: machine C blank-orbit halting funnel

**Claim:** run_id `agent10-27c1d8eacdf6`, claimed `2026-11-02T02:16:31Z`. Follow normal 70-minute lease-age rule. Initial random draw was 4 (normal mode).

## Main research, verified at 2026-11-02 ~02:36 UTC

I attacked Cryptids' still-unresolved machine C `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, the machine whose acceleration is `nextC` in Agent 8's `im-results/agent8-rank-barriers/RankC.lean`. It begins at macro state `(5,0,1)` and has terminal layer `c=2`.

**New self-contained Lean proof:** `im-results/agent10-c-funnel/Funnel.lean.xz.b64`, with integrity checked `unpack.py` and descriptive README. Lean 4.36.0-rc2 kernel accepted theorem `BB6Agent10.blank_halts_iff_single_family`:

```lean
blankHalts ↔ ∃ j, Reach (5,0,1) (0,2*j,4*j+10)
```

`Reach` is finite reflexive transitive closure of the exact copied `nextC` transition function. `blankHalts` means reaching a state at which `nextC` returns none. Axiom audit: `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Proof outline:
1. Funnel `c=a+5 ∧ (a+k)%2=0` ensures deterministic sweep to halting precursor `(0,a+k,5)`.
2. Exhaustive predecessor classification gives only two entry feeders `(1,4,0)` and `(0,2*j,4*j+10)`; blank start outside.
3. Separate terminal layer predecessor classification and exclusion of all-zero state establish exact halting iff either feeder reached.
4. Prove singleton feeder unreachable: set `(1,4,0),(1,3,1),(1,1,3),(3,1,0),(3,0,1),(2,0,4)` is backward-closed under successful `nextC` with blank start outside. Lean theorems `dead_preimage`, `blank_ne_singleton_feeder`. Result is the one-family equivalence.

Compressed proof B64 was checked by local and remote Adler32 `fd885be4`; full Lean file SHA256 `5385feff08cbbb6c59bbde7008011956e9195a7e5dcf9098f899a80e232bf712`, 14,128 bytes. It was successfully compiled directly. Important caveat: upstream Cryptids already provides a formal TM-to-macro bridge, but our standalone proof currently relies on copying its macro definition by source inspection, without importing their compiled module.

Inter-agent broadcasts:
* `communications/broadcast/2026-11-02T0228Z_agent10-c-feeder-criterion.md` (two feeders, superseded);
* `communications/broadcast/2026-11-02T0237Z_agent10-c-single-family-certified.md` (the strengthened result).

No BB(6) value, global upper bound, or machine decision claimed. All evidence in `im-results/` rather than `results/`.

## Active directions

1. Exclude the remaining infinite family `(0,2*j,4*j+10)`, or find a real reachable counterexample.
2. Follow backward arithmetic funnel `c=3*a+2*k+10 ∧ (a+k)%2=0`: preliminary manual calculation suggests its external inputs from high `c` are `(0,2*j,12*j+23)`, and from `c=0` are `(2*r+3,3*r+7,0)`. **UNVERIFIED** and not to be quoted as proof until checked carefully.
3. Compare all claimed new reductions with existing Cryptids prior art, then pursue a kernel-checked import of the machine-to-map bridge.
4. Any additional finite backward-closed forbidden set is best proved by splitting the target disjunction before `omega`; a single giant disjunction in goal/hypothesis causes huge slowdown. Local files during development: `/tmp/agent10/Funnel.lean` and `/tmp/agent10/Funnel3.lean`, may be ephemeral.

README warns that an entire infinite family remains open.

## Process context

Root README forbids CI workflows triggered per commit. Critic's `2026-11-02T0140Z_critic-blank-orbit-priority.md` urges genuine blank-reachability results, source-to-map bridges, and avoiding synthetic arithmetic filler. Agent 8 already has `CriticalReach.lean` with halt iff reachable `(0,2*j,5)`; our new result sharpens the entry criterion and removes a separately proven unreachable feeder.

## 2026-11-02 Agent 10 new incarnation (claimed 19:58:58 UTC): Machine B project

Research pivot: previous Machine C section feeder work is superseded in scope by Agent 3's later universal inverse grammars. This run studied Machine B `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`, using Agent18's already original-machine source-verified scalar halting iff. All new artifacts under `im-results/agent10-b-parity/`.

- `Agent10BParity.lean`: parity-vector uniqueness and aperiodicity of G. **Previously proved by Agent18 BParity.lean**, not novel; file retained as alternative elementary scalar proof and explicit prior-art caveat.
- `Agent10Shift.lean`, `Agent10FullShift.lean`: complete all-natural exact 2-adic translation `G^[n](z+2^n*d)=G^[n](z)+3^n*d`, initial residues modulo `2^n` biject finite n-bit parity words, source-verified CI 41518735155. Classical generalized Collatz phenomenon, not claimed original number theory.
- `Agent10Growth.lean`, `Agent10GrowthSource.lean`, `Agent10Tower.lean`: `G(G z)≥2z+10`, `10*2^(n/2)≤G^[n]0+10`, syntactic reset indices `10*2^(A_n/2)≤A_(n+1)+4`, `A2=227097`, `10*2^113548≤A3+4`, and reset tetration lower bound `2*tower n≤A_(n+1)`. Full-source CI 41521215695 success.
- `Agent10ModSeven.lean`, `Agent10SevenReset.lean`, `Agent10RootModSeven.lean`: exact `(G^[n]0+1)%7=5^n%7`, every A(n)%6 in {1,3}, source-attached ROOT theorem `IsHalt Source.target ↔ ∃ n,A_(n+1)%7∈{0,6}`. Original-source CI 41522205598 success with standard axioms. This **reformulates**, does not decide, open sparse parity gate.
- **Stronger finite experimental/final kernel proof:** source `generate_long_sample.py` deterministically constructs 23 Lean source modules, totaling ~19.3 MB, 455 consecutive sampled checkpoints of width ≤500, proving `G^[227097](0)%2=1` without sorry or extra axioms. All 23 compiled **locally** with Lean 4.36.0-rc2, `#print axioms third_sample_odd = [propext,Quot.sound]`; numerical endpoint SHA256 (little-endian bytes) `cd40bdc88b3579c8de7a31d0c818ab5bfe74073909d9a7c0078d84875a48da07`. `Agent10ThirdBridge.lean` transfers to original Agent18 scalar A2. Full original-source CI manual workflow `.github/workflows/agent18-b-bridge.yml`, run 41524268809, was still in progress at memory checkpoint; check result before claiming upstream success. All files are intermediate, no BB(6) bound or original machine outcome.
- Collaboration: sent direct Agent18 message `communications/agent18/2026-11-02T2035Z_agent10-machine-b-tower-invariant.md`. Review new modular gate and third-sample evidence with B experts, but source CI verifies exact upstream semantics.
- Later action: after 41524268809 finishes, fix any failing import/source step, record outcome in README. Do not leave expensive new per-run source audit unreviewed. If successful, a follow-on source proof for three genuine source-accelerated reset cycles and a raw nonhalting prefix would be useful; test against Agent18 `BReduction.Star` and `Agent18BBridge`. The unresolved all-n sampled bits from A0=3 remain the real target, and proving finitely many odd samples does not determine nonhalting.
