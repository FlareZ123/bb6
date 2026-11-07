# Executable low dyadic tower exclusion

This is an intermediate formalization of Agent19's all-depth low stopping theorem.

## Exact gate

For parameters (n,m), define

[
egin{aligned}
G(n,m) iff {}&
2\le n \land n\equiv0\pmod2 \land n+4\le m \\
&\land (9m+13+5\cdot2^{n+2})\bmod2^{n+4}=0 \\
&\land \left\lfloor\frac{9m+13+5\cdot2^{n+2}}{2^{n+4}}\right\rfloor\le m.
end{aligned}
]

The quotient is the (r) in
[
9m+13+5\cdot2^{n+2}=r\,2^{n+4}.
]
The source theorem `BB6.Agent19SixCone.low_linear_stop_no_root` proves that any such gate excludes the low target
[
(1,\;2^{2m+3}-(3m+4))
]
from the authentic `CReach` orbit.

## Executable Boolean

`lowTowerExcludedBool m` scans `n ∈ [0,m]`. The scan is complete because every gate requires `n+4 ≤ m`. The Lean theorem `lowTowerExcludedBool_iff` proves exact equivalence with the existential proposition, and `lowTowerExcluded_no_root` transports Agent19's theorem to the whole gate.

The gate is a compact all-depth condition. It includes the explicit seed progressions documented in `LowTowerFamilies.lean`, and also tests every admissible even depth and quotient offset directly.

## Scope and remaining work

- This excludes only parameters satisfying the displayed gate. It does not eliminate the entire low branch.
- For example, (m=112) is not covered by this gate and remains a difficult low-root decision instance.
- Smoke checks include (m=11,75,219,539) (excluded) and (m=112) (not excluded).
- The module is kept under `im-results/` because it is an executable interface to an existing exclusion theorem, not a new standalone mathematical result.

## Bounded low-root search experiment

`search_low_roots.py` implements the exact section map, the complete inverse
candidate grammar for states with (y\ge5), and mass-bounded brute-force
predecessors for (y<5). It applies the source normalizers at every inverse
node, which preserves `CReach` by the corresponding source equivalences.
The optimized candidate generator is checked against exact brute-force
predecessor enumeration on 450 small states.

For (m\le200), the transcribed low filter admits 92 values. The inverse
search exhausts all 92 with no blank-root path. The largest tree is (m=112):
614,197 visited states, maximum depth 2,608, maximum branching 11, and no
(y<5) frontier. The all-depth tower gate itself excludes (m=11,75,139)
in this interval. These are finite computational observations only; they
do not prove the low branch impossible for arbitrary (m).
