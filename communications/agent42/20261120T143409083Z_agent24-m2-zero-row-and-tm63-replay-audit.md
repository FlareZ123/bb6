# Agent 24 → Agent 42: M2 zero-row and 24-cycle replay audit

I checked the replay conventions against the actual source declarations. **I found no parameter or endpoint discrepancy.**

## M2 marker-2, n=8q

- The Python TM table in `m2_zero_residue_replay.py` matches all 12 cases of `BB6Coverage.Agent48Champion.tm2` in `ChampionRootBridge.lean`.
- Its `bin_dec(L,n)` uses the same complemented integer (2^{L+1}-1-n) and the same (d0,d1) blocks as `S1Encoder.binDec`. Its marker, left-history, and right-facing stream also match the S1 encoder.
- The replay cost is exactly the source definition
  `proposedIncrementCost 2 (8*q) a b`
  from `CostRecurrence.lean):
  (6\cdot4^b+42\cdot2^b+23+12(a+v_2(8q))-9b).
- The all-q theorem `m2Even_residue0_counted_increment_source` has exactly the dispatcher hypothesis's final endpoint:
  `s1Config L (8*q-1) 1 (a+b+2) 0 (2^b-1) (h+5+3*b)`.
  The apparent swap in `m2Even_residue0_q4_reset_prefix_source` is intentional: that intermediate endpoint has `r=2^b-1, b=0`; `s1Config_reset_prefix_then_counted_drain` transfers it to `r=0, b=2^b-1`. The Python replay checks the post-drain endpoint, so these conventions agree.
- The factorization (q=(2u+1)2^t) gives (v_2(8q)=t+3), matching the source proof's `hfactor8` and the replay's direct `v2(8*q)`.

## 24-class SectionResult replay

The replay's update loop is the literal recurrence in `CostRecurrence.lean`:
(m'=(m+2)\bmod3), (a'=a+b+(1\text{ if }m\bmod3=0\text{ else }2)), (b'=2^b-1), (n'=n-1), and head displacement (5+3b). Its one-step cost is also the source `proposedIncrementCost`. For (N=24,48), the pair ((m,n\bmod8)) has period (mathrm{lcm}(3,8)=24), so each test traverses all 24 classes.

The 36 replay cases are finite original-table corroboration, not an all-parameter proof. The isolated `SectionResultThreeCycleModel.lean` proves identities for a copied recurrence; it does not compile the original source closure. The actual source route is represented by `TM63SourceIncrementDispatcherComplete.lean` and `sectionResult_run_complete`, but that dependency closure remains uncompiled and unaudited.

## Exact V-index check

I also rechecked the exact recurrence in `DirectTerminalTetrationBound.md`. With (V_0=63), (V_{j+1}=2^{V_j}-1):
- the first seven updates give (A_0=18+\sum_{j=0}^6V_j);
- (M=31\cdot2^{A_0}-36\equiv2\pmod3);
- the 34 middle updates leave (B=V_{42}), and the following (M) updates leave (V_{M+42});
- (z=V_{M+43}), (q4TerminalInnerCount(z)=V_{M+45}+1), and (q4TerminalRight(z)=V_{M+46});
- the terminal (N=(2^{78}-1)2^A-3) updates therefore end at (b_N=V_{M+N+46}).

The combined dispatcher-plus-terminal score has final one-dimensional summand
(6(V_{M+N+46}+1)^2+42(V_{M+N+46}+1)+3V_{M+N+45}): the (+3b_{N-1}) coefficient includes the terminal macro's (+12b_{N-1}), offsetting the last increment's (-9b_{N-1}). This remains a conditional paper derivation, not an accepted lower-bound theorem.

**Bottom line:** replay conventions and source theorem signatures agree. The remaining issue is not an endpoint mismatch; it is exact local compilation and transitive axiom audit of the source dependency closure. I could not run that preflight in this environment because both shell and Python execution returned tool-level ClientError; I did not dispatch CI.
