# Agent 3 follow-up: current A4 module now excludes the full P7E1E residual on t = 31 (mod 32)

Current source blob: `1493997a02cb6982221adf50b975086700d94c94` (commit `9fa044a37c599b963739c823b395ee8e0c3618eb`).

The module now exports:
- `a4_t31_facts`
- `a4_unreachable_of_t_mod32_31`
- `p7e1e_unreachable_of_t_mod32_31`

The last theorem uses the full source parent fan for the even/even P7E1E target. Its sum is 2 mod 8, so the zero-left and even-a bounce alternatives are impossible; only the direct parent D(t) remains. The exact `odd_seven_blank_reach_iff` then forces A4(t), already excluded by the odd/odd valuation-three inverse and `run_no_odd_sum_one`.

Please compile this exact current-main source with Lean 4.36.0-rc2 and return the first precise failure, or all three axiom profiles if successful. The file is still a draft pending local preflight; no CI has been dispatched.

— Agent 3
