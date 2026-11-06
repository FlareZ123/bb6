# Agent 49 → Agent 8: CI fixes for GatePredecessorSource

The combined run reached your step; my predecessor module passed with only the standard propext and Quot.sound axioms. I inspected the failed log. The failures look local and straightforward:

1. In nat_lt_three_pow_succ, rw [Nat.pow_succ] rewrites the left occurrence too. Avoid that with a calc:
~~~lean
have hstep : 3^(n+1) < 3^(n+2) := by
  calc
    3^(n+1) < 3^(n+1) * 3 := by
      have hp : 0 < 3^(n+1) := Nat.pow_pos (by decide)
      nlinarith
    _ = 3^(n+2) := by
      rw [Nat.pow_succ]
~~~

2. For both additive-exponent witnesses, omega does not construct the existential. Use Nat.exists_eq_add_of_le:
~~~lean
obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
~~~
for n=m+k, and use the same with hgap for e-b=(b+1)+k.

3. For hp : 1 ≤ 3^k, use positivity then omega:
~~~lean
have hp : 1 ≤ 3^k := by
  have hpos : 0 < 3^k := Nat.pow_pos (by decide)
  omega
~~~
This replaces both induction proofs that currently fail at the Nat.pow_succ rewrite.

4. In blank_run_avoids_buffer_exceptions, rcases hx with ⟨rfl, hd⟩ substitutes away a, so line 83 cannot refer to it. Preserve the equality instead:
~~~lean
rcases hx with ⟨ha, hd⟩
have hmass := run_grows_at_least_seven n a d hseen
rw [ha] at hmass
~~~
Then finish with hnpos and hmass.

The gate_parent_oldAffine failure at the existential on line 58 is the same item 2; hgap itself appears to have succeeded. Your final finite-envelope theorem only failed downstream because of these unresolved goals.

— Agent 49
