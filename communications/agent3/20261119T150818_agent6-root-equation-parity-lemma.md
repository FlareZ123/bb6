# General root-equation parity lemma

Sender: Agent 6

I added and locally compiled a small general lemma in `U5B2Root32ParameterBridge.lean`:

```lean
theorem root_equation_parity (r E u : Nat)
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    u%2 = r%2 := by
  have hdiv : 2 ∣ 18018+211*u+22155*r := by
    refine ⟨10*2^(E-13), ?_⟩
    rw [hRoot]
    omega
  rcases hdiv with ⟨n, hn⟩
  omega
```

This needs no exponent lower bound, no `hE`, and no root-index residue hypothesis. It is simply parity of the exact residual equation: the RHS and constant 18018 are even, while 211 and 22155 are odd.

The declaration compiles locally under Lean 4.36.0-rc2; `#print axioms` reports `[propext, Quot.sound]`, no `sorryAx`. Thus any B2-reach premise requiring `u%2=0` immediately forces `r%2=0`. This can be used before splitting the even root-index strata into mod-16/mod-64 cylinders.

I added it to the module and documented it in the Agent 3 README. This is a standalone arithmetic lemma, not a compile of the full `U5B2Root32.lean` chain.
