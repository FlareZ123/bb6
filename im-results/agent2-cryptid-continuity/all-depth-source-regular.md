# All positive-depth prepared regular D runs: exact original source composition and time lower bound

**Agent 2, 3 November 2026. Status:** new exact original six-state source-connected universal Lean composition; independent primitive regression. This is an **intermediate theoretical result** about *synthetic prepared F/0 input tapes*. It does **not** prove the actual blank-start D orbit reaches any input in this family, does **not** decide whether the D machine eventually halts from blank, and supplies **no new lower bound on BB(6)**. Research novelty relative to external literature has not been established. Keep under `im-results/` until external review.

## Main theorem: every positive depth has a source-certified long finite run

The fixed original two-symbol six-state Turing machine is
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

Write `I_n(s)` for a state-F configuration scanning **0** with blank tape to the left and physical right tape `1^n s 0^∞`. Let `P_q=(01)^q`. The prepared inputs are regular words
`X(k,q)=I_(3k+4)(P_q 1)`.

For **every natural m≥1**, `BB6.EAllDepthSource.all_positive_depth_original_source` supplies finite parameters `k,q,U,p` with `1≤U<512`, such that the input is `X(k,q)`, its finite right support satisfies
`3k+4+2q+1 ≤ 120·3^m`, and its actual original-machine run contains **three designated preliminary physical F/0 endpoints and m further exact first-return E ladder endpoints**, reaching

```text
I_(3·8^m·U+1) (0 (10)^(p+2m) 1^3 0 1^6)
```

after exactly

```text
firstCost(t,h) + secondCost(t) + thirdCost(v)
                    + totalCost(m,U-1,p)
```

primitive steps, where `thirdCost` denotes the B-version for even m. The **E stage alone** satisfies `totalCost(m,U-1,p) ≥ 64^m`. Physical equality is proved as `BoundaryPadding.ObsEq`, which identifies only the physically irrelevant blank-tape padding, retaining the exact state, scanned symbol, head orientation, and nonzero tape support.

The two exhaustive, constructive parameterizations are:

* **Odd m=2r+1, r≥0:** `v_0=4`, `v_(r+1)=9v_r+4`, `k=9v_r+4`, `q=3r+6`, `U=256`, `p=4`, `t=3v_r+1`, `h=3r+3`. Third endpoint after initial two E macros followed by an E-triple macro:
  `I_(512v_r+257)(P_4 0 1^(6r+6) 0 1^6)`.
* **Even m=2r, r≥1:** `U_0=315`, `U_(r+1)=57U_r mod512`, `v=(3^(m+1)U_r-433)/512` (nonnegative integer by proved residue), `k=9v+7`, `q=3r+3`, `p=1`, `t=3v+2`, `h=3r`. Third endpoint after two E macros followed by B:
  `I_(512v+434)(P_1 0 1^(6r+3) 0 1^6)`.

The third endpoints are **identical** to the E-ladder input
`I_(3^(m+1)U+1)(0 (10)^p 1^(3m+3) 0 1^6)`. The stage's all-depth primitive runtime is the fully source-certified `ETripleLadderSource.totalCost`; see [exact closed form](verification-note.md). We prove source arithmetic `DCostLower.totalCost = ETripleLadderSource.totalCost` for all parameters with **zero axioms**, preventing accidental substitution of independent model recurrences.

**A distinction about endpoint minimality:** within the final m E macro steps, strict first F/0 return minimality is separately Lean-proved in `ETripleLadderSource.level_returns_exact`. For the preliminary first three steps, the theorem certifies specified raw-time F/0 endpoints, without asserting they are necessarily the only physical F/0 checkpoints in those intervals. This does not weaken the exact final primitive-time or nonhalting-prefix results.

## Proven no-halt prefix

`ERegularLadderSafe.lean` proves that halting is absorbing in the original raw transition table, and any end-of-run physically observed F/0 state excludes a prior halt. It instantiates this for both three-plus-ladder branches, at **every primitive time up to and including the exact total runtime**.

`EAllDepthSafe.lean` lifts this to every m≥1: for a prepared regular input of at most `120·3^m` bits, the machine is *provably nonhalting at every primitive time t≤64^m*. This is a source-level mathematical statement of a **supercubic input-size runtime lower bound** for infinitely many **nonblank prepared inputs** (exponent `log_3 64 ≈ 3.78558`). It does not imply any corresponding lower bound on the canonical blank-input Busy Beaver value.

**Final directly physical formulation:** [`EInputLengthSafe.lean`](EInputLengthSafe.lean) removes the remaining shorthand between symbolic `k,q` and real initial tape size. It proves `start_is_regular` as exact configuration equality, `regular_right_length` as the exact list length, and the particularly simple theorem

```lean
BB6.EInputLengthSafe.bounded_tape_unbounded_raw_runtime
  (m : Nat) (hm : 0 < m) :
  ∃ c : CryptidBoundary.Cfg,
    c.st = 5 ∧ c.l = [] ∧ c.h = false ∧
    c.r.length ≤ 120 * 3^m ∧
    ∀ t, t ≤ 64^m → (CryptidBoundary.run t c).st ≠ 6
```

This is an independently checked, **concrete original six-state machine configuration-size versus primitive runtime theorem**, with no implicit conversion from paper tape encoding. [Exact source CI 41702472297](https://github.com/FlareZ123/bb6/actions/runs/41702472297) **succeeded**, showing precisely `[propext, Quot.sound]` as axioms, with no `sorryAx`.

## Reproducibility and trust boundary

- [Exact universal third F/0 E/B branch](EThirdSource.lean) imports original `ESecondSource`, `CryptidTriplePairs`, `BoundaryPadding`. Both congruence branches are independently proved for every parameter.
- [Exact three-plus-m source composition](ERegularLadderSource.lean) connects these two branches to the already source-certified all-depth E-ladder without replacing actual physical observations by literal padded-list equality.
- [Full all-depth source existential](EAllDepthSource.lean) imports earlier mathematically proved `DComplexity.all_depth_synthetic`, aligns its cost definitions, and establishes the true original-source machine run for every positive depth.
- [No earlier halting lemma and branch certifications](ERegularLadderSafe.lean) and [universal no-halt prefix](EAllDepthSafe.lean) make the halting-time implication explicit.
- [Literal primitive simulator](check_original_regular_depth.cpp) uses only the 12 transition-table entries, a sparse tape and an exact full-tape comparison at the predicted endpoint, with no Lean imports or accelerator. Its two regression cases are:

| m | k | q | finite support | exact total primitive steps | final unary run | full tape |
| ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 1 | 40 | 6 | 137 | 8,263,623 | 6,145 | matched |
| 2 | 16 | 6 | 65 | 9,885,171 | 6,721 | matched |

All source assertions use pinned Lean **4.36.0-rc2** and unchanged original D transition source recovered from SHA-locked `Boundary.lean.xz.b64` in the GitHub workflow `agent2-d-third-source.yml`. [Original-source full all-depth CI run 41700420808](https://github.com/FlareZ123/bb6/actions/runs/41700420808) **passed**, with `[propext, Quot.sound]` as the only axioms for the main theorem, no `sorryAx`. [Complete source plus nonhalt and independent simulator run 41701434773](https://github.com/FlareZ123/bb6/actions/runs/41701434773) **passed**, with the two primitive checks exact. **Final full original-source Lean and primitive regression CI [41701897271](https://github.com/FlareZ123/bb6/actions/runs/41701897271) SUCCEEDED.** It compiled unchanged source code for all dependent machine lemmas, the universal `regular_prepared_no_halt_through_64pow` theorem and independent C++ primitive checks. The final no-halt theorem has axiom set exactly `[propext, Quot.sound]`, no `sorryAx`; the same holds for `odd_chain_no_halt` and `even_chain_no_halt`. Both raw tests report matching full physical tapes.

## Open next step toward BB(6)

This theorem establishes abundant very long **finite** original-machine runs under prepared inputs. A certified connection from the machine's **genuine all-blank A start** to any chosen `X(k,q)`, or an invariant excluding halt throughout the entire actual blank orbit, remains unavailable. In particular, the Agent35 eleven-rule `DRegular.next` symbolic language model still relies on an unproved all-row original-source `SourceContract` and a global grammar closure claim; these gaps must be filled before model trajectories become authentic blank-root results.

This result is a reproducible tool for studying exceptional packet behavior and testing candidate invariants. Its novelty and relevance as a publishable finding remain subject to independent literature review.
