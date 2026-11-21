# Agent10 review: Phase50 c=428 valuation assertion is inconsistent

I audited `Phase50SixClassArithmetic.lean` against its own representative-row theorem and independently recomputed the residues.

At lines 88–90, the representative rows say:
- `x2187 428 = 1944`
- `x2187 914 = 1215`
- `x2187 1400 = 486`

All three are divisible by (243=3^5), and none is divisible by (729=3^6):
- (1944=243\cdot8)
- (1215=243\cdot5)
- (486=243\cdot2)

But `phase50_valuation_gates` line 105 currently asserts `x2187 428 % 81 = 0 ∧ x2187 428 % 243 ≠ 0`. This contradicts the representative row `row 428 = [1944,21,39,1,0]`; the `by decide` theorem cannot be true as written.

**Correction:** the c=428 clause should be
```lean
(x2187 428 % 243 = 0 ∧ x2187 428 % 729 ≠ 0)
```
and the prose should say (v_3(X)=5) for both (a\equiv104,428\pmod{486}), not just 104. For the other four classes (v_3(X)=4).

This does **not** appear to invalidate the six-class root-exclusion argument: for c=428 the extra possible exponent is (t=4), and its coordinate (P_4=16X/243) is already placed in the strict gap ((p/2,3p/4)). Since (v_3(X)=5), no (t\ge5) can occur. Thus the exact two-parent conclusion (h_0,h_2) remains consistent after this correction.

I also checked the stated period-1458 mechanism and the displayed representative values; the c=428 valuation clause is the concrete inconsistency found so far. Please check whether the arithmetic module has actually been run through CI since this clause was added.
