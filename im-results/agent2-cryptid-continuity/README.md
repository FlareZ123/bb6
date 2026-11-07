# Cryptid D: source-certified return grammar and 3-adic synchronization

**Research state (6 November 2026): exact return and shift theorems for specified source configurations; no global true-blank halt/nonhalt decision.** [Complete working proof record](FULL_RESEARCH_LOG.md).

## Original machine and proven scope

The D-start table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. The original `I_n(r)` F/0 section has blank left tape, leading unary `1^n` and suffix `r`. Physical blank-padding and first-return conditions matter when composing source steps.

- [BlankEighthRejoin.lean](BlankEighthRejoin.lean) source-certifies another actual-blank exceptional return after 6,046 regular source steps, with successful [original-source CI 41870046802](https://github.com/FlareZ123/bb6/actions/runs/41870046802). This is finite authentic continuation without a perpetual-survival conclusion.
- [DRegularShift.lean](DRegularShift.lean) proves for the canonical eleven-row regular return model, without the earlier conditional shift hypothesis, an all-depth `3^k` input/`8^k` output shift identity, including matching success and failure at regular exits. [CI 41872704046](https://github.com/FlareZ123/bb6/actions/runs/41872704046). [DRegularSourceShift.lean](DRegularSourceShift.lean) transports paired regular runs to the physical original six-state machine: [CI 41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993).
- [DRegularDurationShift.lean](DRegularDurationShift.lean) and [DRegularTimedShift.lean](DRegularTimedShift.lean) give exact quadratic runtime dependence for `k` regular returns, with `55 Q_k + 12·9^k = 12·64^k`: [CI 41875379548](https://github.com/FlareZ123/bb6/actions/runs/41875379548). The physical-source timed composition and exceptional-packet extensions have their own dependencies, explained in the [full synthesis](2026-11-04-eighth-and-3adic-synchrony.md).
- Further source-certified lemmas describe a guarded E-boundary halting cylinder, B-run valuation, a universal **synthetic** unary halting extension, and precise E111 first-return conditions. All exact theorem references remain in the [full research log](FULL_RESEARCH_LOG.md).

## Unresolved root problem

Regular all-depth synchronization does not establish that the actual blank orbit remains regular at **every** return. Exceptional exits, physical suffix equivalence and possible original halts need complete treatment.

**Next proof:** establish a blank-root forward-closed word/suffix invariant across every exceptional packet, or produce an original-machine halting witness. A large finite trace or synthetic halting extension cannot settle the blank trajectory.


## Exact 3-adic block evaluation for long regular runs (7 November 2026)

**DRegularFast.lean** turns the all-depth shift theorem in **DRegularShift.run_shift** into an exact block evaluator. For a canonical section s and block length k, write

    s.a = 2 + ((s.a-2) mod 3^k) + 3^k * ((s.a-2) / 3^k).

The small representative is evaluated for k regular sections. The exact shift theorem lifts its endpoint by 8^k times the quotient. The file proves **run_block**, the multi-block evaluator **fastRunBlocks**, and the arbitrary-length identity

    DRegular.run n s = DRegularFast.fastRun n s.

The current block size is 512. This is an exact evaluator for the eleven-row DRegular model, not a new theorem about the original machine.

**Local validation (Lean 4.36.0-rc2):** a standalone kernel computation evaluated the 12,588-step twenty-first regular segment from the actual symbolic-root seed, represented as a 116,926-bit integer (SHA-256 6058f62d1da9808c0da7609037f59cfe61fba7ceadf9dc0886dfbc25d66b9781). It produced the 134,738-bit endpoint (SHA-256 3e2c1a9d3ca8c6b80cd32917a32601966814ec5f0718f48ff6dc2ff60fbbf767), with shape L(9*t21+4,8,1) and t21 mod 27 = 6. The explicit fastRun computation plus endpoint check compiled in 9.36 seconds with 1.5 GB maximum RSS; the endpoint computation itself is by decide and has no axioms. The generic equality theorem inherits the axiom profile of DRegularShift.run_shift ([propext, Classical.choice, Quot.sound]).

**BlankTwentyFirstRejoin.lean** now uses DRegularFast.fastRun for this long segment, and the manual root-chain workflow compiles DRegularFast.lean before it. The earlier root-chain run [42377931873](https://github.com/FlareZ123/bb6/actions/runs/42377931873) was cancelled at the verification step and predates this optimization; it is not a Lean failure report. A fresh manual source-only run is still required to certify the updated composition.

## Conditional blank-root arithmetic lookahead through exception 100

The Python DRegular model was extended beyond the existing twentieth/twenty-second root candidates. Conditional on the preceding root reentries being valid, it predicts exceptional sections through #100. This is an arithmetic lookahead, **not** an original-source proof of those reentries. The most useful branch observations are:

- #24 and #27 are E/E packet returns with p=9 and p=15, respectively; their normalized packets enter A,p divisible by 3 and close through the existing A-zero source boundary.
- #33 is L(27u+7,5,1); two E returns give an A packet with p=7, then the A-one boundary closes it.
- #44 and #45 use the EEE escape family. #44 reaches B then A,p=2; #45 reaches A,p=2 directly. Both are candidates for APacketMarkerSource.A_two and return to L(a,4,0).
- #47 reaches E,p=2 with reset index k mod 9 = 6, so the already source-certified e_two_k0_regular family applies.
- #58, #68 and #90 normalize E/E packets to A,p=5,2 and 11, respectively, and are candidates for A_two; #64 and #78 normalize to A,p=13 and 7, respectively, and are candidates for AOnePacketBoundarySource.a_p1_boundary.
- #82 and #93 use the EEE escape and reach A,p=2. #92 uses the two-E/A-one route.

The A,p=2 closure is supplied by APacketMarkerSource.lean, whose composition is not yet included in the successful unchanged-source CI run 42359163994. These root-specific uses remain provisional until a source-only workflow compiles the exact chain. No k mod 9 = 4 or 7 E,p=2 reset was encountered in this finite model lookahead through #100, but that observation is not a proof of an invariant and does not remove those residual classes from the general problem.
