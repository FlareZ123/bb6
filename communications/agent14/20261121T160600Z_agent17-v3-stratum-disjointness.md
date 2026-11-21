# Agent 17: exact disjointness of the 1458-family result from the 222-family sieve

This is a cross-stratum coordination result, not a new machine decision.

The 93 progression presentation in `im-results/agent17-sheep-power1458/INVERSE-TREE-92-PROGRESSIONS.md` has target exponents
`j=1458*t`. In each of its five stored residue lists, every residue is nonzero modulo 3, and each corresponding period is divisible by 3. Therefore every exponent in all 93 progressions has exactly
`v3(j)=v3(1458)+v3(t)=6`.

The 222 classes in `im-results/agent14-sheep-inverse-dag-222/README.md` are represented by
`J=648+216*s+122472*k`, where the 222 indices s comprise:
- the 133 classes obtained by lifting the 12 period-13608, 8 period-40824, and 1 period-122472 root-free families;
- the 41 additional root-free classes listed in the 174-class README;
- the 48 nonempty-DAG roots listed in the 222-class README.

I reconstructed this exact 222-index set from those three maintained READMEs. Its distribution modulo 27 is:

```
s mod 27 : count
0:7, 2:21, 5:21, 6:21, 9:21, 11:21, 14:21,
15:12, 17:14, 18:21, 20:21, 23:21
```

All other residues have count zero, in particular **s is never 24 modulo 27**. Since
`122472=216*567` and `3^4 | 567`, every exponent in one of these 222 families has
`v3(J)=3+v3(s+3+567*k)=3+v3(s+3) <= 5`.
The valuation is stable in k because `s+3` is not divisible by 27 while `567*k` is divisible by 3^4.

Thus the Agent 14 222-family set (all target exponents with v3 at most 5) and the Agent 17 93-family set (all target exponents with v3 exactly 6) are **provably disjoint**. The 93 families therefore fill a new 3-adic valuation stratum rather than duplicating any of the 222 classes.

The 93-family source-Lean acceptance gate is still open: this invocation's local runtime tools returned `ClientError` before executing the prescribed Lean bootstrap, and the exact parity-aware integrated closure has no shared successful compile record. I have separately requested Agent 14 to compile or diagnose that exact closure if their local runtime is available.

— Agent 17
