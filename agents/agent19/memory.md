# Agent 19 persistent research memory

Claimed 2026-11-02T04:11:00Z under lease `bb6-20261102-agent19-harbor`, selected normal mode on genuine RNG draw 5.

## Verified result (2026-11-02, 04:29 UTC)

Closed the local-to-upstream machine semantics gap for P1 holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. Proof in `im-results/agent19-p1-source-bridge/{P1Bridge,P1HaltingBridge}.lean` verified by manual CI run https://github.com/FlareZ123/bb6/actions/runs/41388451571 against pinned DeepMind Cryptids `ced8f9f44f67a167d5ecc03e687b048c67926371`, Lean 4.35.0-rc4.

Final kernel-checked `BB6.P1Bridge.raw_halts_iff_sparse_gate`:

```
IsHalt original-machine.target ↔
∃ n, HaltingFunnel.ReachT 2 1 2 (14*2^n - 2*n - 10)
```

Axiom audit `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Uniform source G and T equivalence, isValidAcceleration transport, and local HaltsIn↔CollatzHalts proof included. `README.md` documents complete chain. CI `.github/workflows/agent19-p1-bridge.yml` manual only, and `prepare_modules.py` adapts standalone Agent4 Lean files for upstream's module system in temporary CI working directory. First three CI attempts failed due missing .olean import path and legacy non-module restriction; fourth succeeded after directing outputs to `.lake/build/lib/lean` and applying module headers.

This result **does not decide P1 halting** or BB(6). Preserved at `im-results/` rather than `results/`. Broadcast `communications/broadcast/2026-11-02T0431Z_agent19-p1-upstream-proof.md`.

## Research map

`im-results/2026-11-02-cross-holdout-decision-gates-agent19.md` summarizes exact blank-entry systems and remaining iff-gates for P1/B/C/Sheep/D. Critic broadcasts at 01:40 and 03:50 warned of low-value repeated finite residue exclusions, urged global closure.

P1 Agent4 `BlankCriterion.lean` proves exact target family; Agent12 `AllOddCritical.lean` excludes odd n>=3, `AllFourCritical.lean` excludes n>=4 divisible by four. Agent7 rank certificates exclude n0..8. Remaining infinite indices n≡2 mod4, n>=10, are the decisive unknown. Machine B Agent18 has separate *successful* source bridge; C diagonal gate `(0,2j,4j+10)`; Sheep exponent inverse sieve 3544/5400 classes, many open.


## Verified beyond initial upstream bridge (2026-11-02 04:49 UTC)

- `im-results/agent19-p1-source-bridge/ResidualGateway.lean` exact reachable gateway theorem for every `d≥10,d%4=2`: `BlankReach 2 d ↔ BlankReach (d-6) 3`. CI [41389242182](https://github.com/FlareZ123/bb6/actions/runs/41389242182) passed. Critical specialization n%4=2 is partially redundant with Agent7's existing stronger critical-specific `CriticalFeeder.lean`; no claimed novelty.
- `im-results/agent19-p1-source-bridge/GDepth.lean`: exact all-k,c equality between Agent1 and Agent4 G plus **complete if-and-only-if inverse fiber classification** for arbitrary `G(k,c)=(b,d)` with b>0 and `(d+b/2+3)%8=4`. The shifted weight limits recursive inverse depth to 0,1,2, with explicit three arithmetical shapes (see `INVERSE-CLASSIFICATION.md`).
- `im-results/agent19-p1-source-bridge/TwoFeeder.lean`: **exact all-time actual-blank-orbit two-feeder iff** for all `K%8=2`:
  `BlankReach (4*K+4) 3 ↔ BlankReach (2*K-4) (2*K+9) ∨ BlankReach (3*K-2) (K+5)`.
  It rules out the third source inverse shape using Agent4's global positive-even-left residue invariant. Both remaining branches realized by exactly 2 T steps. Critical specialization n>=18, n%16=2. **Fully kernel verified on genuine local imports, Lean 4.36.0-rc2, CI [41390551413](https://github.com/FlareZ123/bb6/actions/runs/41390551413)**. Axiom audits only `[propext, Classical.choice, Quot.sound]`, no sorryAx.
- `im-results/agent19-p1-source-bridge/INVERSE-CLASSIFICATION.md` documents exact theorem, derivation, proof audits, limitations, experiment `K=18` where first feeder `(32,45)` is actually reachable from blank. This forbids any claimed universal feeder-unreachability over arbitrary K.
- Broadcast `communications/broadcast/2026-11-02T0452Z_agent19-p1-two-feeders.md` informs other researchers. Manual-only CI `.github/workflows/agent19-p1-gdepth.yml` verifies imported GInverse, Agent4 full prerequisites, ResidualGateway, TwoFeeder.

## Next substantive goals

Use exact special arithmetic `K_n=7*2^(n-1)-n/2-5` for n=16q+2 (n>=18) to exclude **both** reachable feeder families. For q classes parity, the second family input G's shifted weight has varying 2-adic valuation, so generic all-K argument may fail. Explore additional inverse depth, invariants specific to the critical `K_n`, and whether first feeder relation c=a+13 is ruled out only for sparse K_n (not universally; K=18 is reachable). Seek genuine halt/nonhalt decision, avoid accumulating trivial residue tables.

## Earlier investigation

Candidate **uniform residual gateway** for P1:

```
∀ d >= 10, d%4=2 →
  (BlankReach 2 d ↔ BlankReach (d-6) 3).
```

This is a direct generalization of Agent4 `ThirdTarget.lean` at d=42, relevant to all remaining critical n≡2 mod4. Its proof uses `T_to_two_positive`, `T_odd_left_predecessor`, and `blank_even_left_invariant` (from Agent4 `NoSecondTarget.lean`). A standalone skeleton with exactly the expected lemma types **compiled** Lean4.36.0-rc2 at local `/tmp/bb6a19/ResidualGatewayMock.lean` with abstract assumed inputs; still needs actual import compilation and corollary for n. It is only a candidate until source-verified. The earlier first attempt using dependent `cases` failed; generic `last_predecessor` induction lemma solved dependent elimination and compiled in mock.

Other local scratch tests: `/tmp/bb6a19/HaltingBridgeMock.lean` formally checked iterator equivalence skeleton before upstream run. Python `p1_stats.py` explored 2M T steps from (2,1), found no halt; only exploratory, no new theorem.

## Next steps

1. Create and CI verify full `ResidualGateway.lean` using actual Agent4 imported lemmas and original-machine bridge, capture axiom audit. Package corollary targeting n%4=2 if feasible.
2. Seek uniform exclusion or explicit blank reachability for residual odd-sector gateway (d_n−6,3). Avoid superficial residue-density increases.
3. Continue research, communicate useful results and preserve exact evidence.
4. Mandatory after every checkpoint: compare real UTC clock with `claimed_at=04:11:00Z`. Continue until elapsed >=70 min, then orderly release by pushing memory, deleting and pushing lease **as final mutation**. Do not end earlier.

