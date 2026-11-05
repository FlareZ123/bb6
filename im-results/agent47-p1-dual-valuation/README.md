# P1 dual feeder 2-adic inverse-depth complementarity

**Agent 47, 2026-11-05.** Intermediate mathematical research about the authentic P1 two-feeder decomposition. It neither decides P1 nor establishes an upper bound for BB(6).

## Existing source-verified reduction

Agent45's original-source theorem *two_sector_critical_iff_feeders*, successful CI [41438844462](https://github.com/FlareZ123/bb6/actions/runs/41438844462), establishes that for each q≥1 the critical reset at n=16q+2 is blank-reachable exactly when at least one of two sparse feeders is reached. Write X=2^(16q), u=7X−4q−3. The feeders are L1=(4u−4,4u+9) and L2=(6u−2,2u+5).

Agent45's earlier theorem *l1_all_powers* proves that the first feeder G-inverse shift S1=6u+10=42X−8(3q+1) satisfies (2^(t+3) divides S1) iff (2^t divides 3q+1), for every q≥1 and all t. This first result is established prior work.

## Exact complementary second-feeder result

The second feeder shift from the source GAncestor grammar is S2=(2u+5)+(6u−2)/2+3=5u+7=35X−4(5q+2).

The new Lean theorem **BB6.P1DualValuation.shift_all_powers** proves for every q≥1 and every t that **(2^(t+2) divides S2) iff (2^t divides 5q+2)**. It handles all exponents. The proof uses the exact bound 4(5q+2)<X and separates t+2≤16q from larger exponents.

**BB6.P1DualValuation.feeder_factors_coprime** proves gcd(3q+1,5q+2)=1 for every q, as 3(5q+2)−5(3q+1)=1. Consequently the two feeders cannot simultaneously have extra powers of two beyond their respective base valuations:
- For even q, the first shift has exact valuation three; the second can have additional powers.
- For odd q, the second shift has exact valuation two; the first can have additional powers.

The original source GAncestor_power theorem characterizes every positive-output inverse through an exponent t. Our source-linked **BB6.P1DualSource.odd_second_feeder_inverse_depth** shows that for odd q every GAncestor of L2 has some such exponent at most **2**.

## Code, checking and provenance

- [P1DualValuation.lean](P1DualValuation.lean): self-contained Lean 4.36.0-rc2 arithmetic proof, locally compiled with standard axioms only, no sorry or unsafe.
- [P1DualSource.lean](P1DualSource.lean): imports Agent45 P1TwoSector and Agent1 GInverse and connects the exact valuation to genuine GAncestor semantics. Locally compiled with signature-matching reduced copies of these imported declarations, without sorry. The local check is not an original-source audit.
- [Manual-only Lean CI](../../.github/workflows/agent47-p1-dual-source.yml) compiles unmodified repository dependencies and the two new modules with an axiom audit. [CI run 41962883558](https://github.com/FlareZ123/bb6/actions/runs/41962883558) was initiated via [issue 11](https://github.com/FlareZ123/bb6/issues/11). **Check the run conclusion before citing full original-source certification.**

## Consequences and next test

The two feeder **first inverse fans** have complementary guaranteed shallow cases, suggesting a parameter-adaptive inverse strategy. This does not bound total predecessor depth; Agent27/33/45 proved arbitrarily deep synthetic inverse paths. Neither feeder is shown blank-unreachable and both n≡2 and n≡14(mod16) sectors remain open. A full surviving feeder exclusion or a genuine blank-origin halting witness would be consequential.

**Novelty caution:** The coprimality/parity identity is elementary. The incremental work is the all-exponent second shift and its link to original G-inverse semantics. Preserve in im-results pending independent relevance and novelty assessment.
