# Agent 7: rank-bracketing certificates for nine P1 halting gateways

**Status: reproducible intermediate theorem, not an original BB(6) machine decision.** This investigation concerns the exact independently transcribed accelerated map of the six-state two-symbol machine
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.
Its certified blank-tape entry state is `P1(2,1)`. The machine-to-accelerator correspondence is established in [DeepMind Cryptids' source module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean). Our Lean source imports Agents 1's standalone transcription in `im-results/agent1-p1-map/GParity.lean` and `Packet.lean`, rather than importing the large upstream machine bridge.

## Main exact statement

Let `T` be that acceleration and `iterT t (2,1)` the option-valued result after exactly `t` successful accelerated transitions. Let `critical(n)=14*2^n-2*n-10` for natural `n`.

**Kernel-checked theorem `BB6.Agent7.no_first_nine`:**

```lean
∀ i : Nat, i ≤ 8 →
  ∀ t : Nat, iterT t (2,1) ≠ some (2,critical i)
```

Equivalently, the actual entry orbit avoids `(2,4)`, `(2,16)`, `(2,42)`, `(2,96)`, `(2,206)`, `(2,428)`, `(2,874)`, `(2,1768)`, and `(2,3558)` at *all* finite times. Agent 4 had previously given structural backward certificates for the first two, so the remaining seven exact exclusions extend that verified finite subset. This is a finite-target exclusion. It leaves infinitely many critical targets open.

The fully general analytic lemma `no_target_bracket` states that if two consecutive, exactly certified actual-orbit hubs `p→q` bracket a target's strictly increasing rank `a+c`, and `q` differs from that target, then the target is unreachable at any finite time. Proof: for all earlier times, monotone rank is at most `rank(p)`; at the crossing time it is `q`; at every later time the rank exceeds `rank(q)`. Rank strictness for every surviving `T` transition is imported from Agent 1's Lean `T_mass_increases`.

The first nine brackets were:

| n | c=critical(n) | Last mass below target, index / hub | First mass at or above target, index / hub |
|---:|---:|---|---|
| 0 | 4 | 1 / (4,0) | 2 / (2,5) |
| 1 | 16 | 8 / (0,17) | 9 / (3,15) |
| 2 | 42 | 23 / (27,15) | 24 / (32,13) |
| 3 | 96 | 55 / (8,89) | 56 / (11,87) |
| 4 | 206 | 110 / (163,43) | 111 / (76,135) |
| 5 | 428 | 219 / (272,157) | 220 / (275,155) |
| 6 | 874 | 438 / (619,255) | 439 / (736,141) |
| 7 | 1768 | 861 / (152,1617) | 862 / (155,1615) |
| 8 | 3558 | 1741 / (1980,1579) | 1742 / (1983,1577) |

Note that the final certified trace also includes one state after these bracket indices. All listed hubs are *accelerated configurations*, and the index counts `T` applications.

## Verification design

- `RankBase.lean` imports `Packet`, proves that a structurally fuelled and kernel-reducible `Gfast` equals the original well-founded `G` for **all** natural arguments, and that `Tfast=T` for **all** inputs. This avoids the computational opacity of the well-founded `G` in ordinary `decide`.
- `RankCertificate.lean` contains 192 indexed checkpoints and verifies each intervening block of at most 10 exact accelerated steps with Lean's `decide`. These are definitional kernel checks through `Tfast_correct`; no `native_decide` or untrusted native evaluation is used.
- The general rank argument, the nine target exclusions, and `no_first_nine` are fully quantified over arbitrary future time. A local Lean 4.36.0-rc2 check with a signature-compatible standalone `Packet` compiled successfully. The dedicated manual GitHub Actions workflow `agent7-p1-brackets-lean.yml` rebuilds against the **actual** repository `Packet.lean` and checks axiom reports.
- Axiom reports for the local proof: `[propext, Quot.sound]` for `no_first_nine`, `no_target_bracket`, and sample `no_critical_0`. No `sorryAx` in successful checks.
- No workflow runs on every commit, following the root repository's CI budget rule.

## Limitations and next steps

This certificate uses exact finite computation followed by a rigorous all-time rank argument. It is reproducible and more economical than an exhaustive backward-predecessor tree for these specific thresholds. It does **not** furnish an invariant excluding the infinitely many `critical(i)` with `i≥9`; no claimed BB(6) lower/upper-bound improvement follows. All material stays in `im-results/`.

Potential research use: extend to later thresholds using chunked certificates, optimize proof compression via block accelerations, or extract new modular patterns in first-crossing configurations that permit a genuinely infinite family theorem. The latter would be more substantive than simply increasing a finite cutoff.
