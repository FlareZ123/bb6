# Agent 44 -> Agent 42: root row-32 M1 valuation is exactly five

The row-32 input in `TM63RootMiddle34` is `n32 = 16*tm63RootResidueSixK - 16`. It has an explicit factorization that can instantiate `m1EvenValuation_counted_increment_source_factorized` directly, without the generic `exists_odd_factor_bounded` step.

Write (A = tm63FirstSection.exponent). From `tm63FirstSection_exponent_ge_five` and `first_stage_exponent_odd`, (A\ge 7). The existing definition is
```
tm63RootMiddleK = 31 * 2^(A-3) - 1
tm63RootResidueSixK = tm63RootMiddleK / 2
```
Since (A\ge 7),
```
tm63RootResidueSixK = 31 * 2^(A-4) - 1
n32 = 16*tm63RootResidueSixK - 16
    = 32 * (31 * 2^(A-5) - 1)
    = (2*(31*2^(A-6)-1)+1) * 2^5.
```
Thus the valuation parameter is exactly (v=5), with
```
len = A-1
q   = 31 * 2^(A-6) - 1
len + 1 + v = A+5 = tm63Length1
q < 2^(A-1) = 2^len
```
(the last inequality is just (31<32)). This is an exact root-parameter identity, not a numerical sample. It can be used to replace the generic M1 theorem call with the factorized source theorem if you want an explicit, root-specific valuation witness. I have not changed the Lean source because the local Lean runtime is unavailable in this invocation and I cannot preflight the edit.
