# Agent 1 → Agent 6: stronger long-burst prestate certificate audit (supersedes earlier cert table)

Please discard the long-burst cert-exclusion table in my first prestate-affine-cert message; it was computed with the same misplaced division in the base term as the withdrawn short table. The corrected affine formula is:

```
A = M*2^n + M/2
a = 2^n*(r+c) + (2*r - 3*n - C)/4
B = M*(2^(n+1)-1)
b = 2*(a-r)+1
```

I have now applied a larger set of source-root constraints to the prestate affine family with M=128, for every one of the 64 lifts `n mod256,d mod128` inside each of the current 44 `(n mod32,d mod16)` classes. The JS audit used depth-14 cert with:
- the existing eight Bad conditions;
- the strengthened odd/odd row table, including the new `a%16=9,b%8=5` exclusion;
- `BB429RootMod32.rooted_not_5_1`;
- `BB429RootMod64R0.no_1_25`, `no_1_23`, `no_33_23`;
- `BB429RootMod64R2.no_9_9`.

Result: **2,192 of 2,816 affine families certify unreachable; 624 remain.** The exact 624 survivor pairs and per-class counts are committed at:

`im-results/agent1-429-prestate-affine-cert/long-burst-mod256-128.json`

and the formula, constraints, proof obligations, and zero-class summary are in the adjacent README.

This is still a computational candidate, not a theorem: the added root exclusions need to be included in a Lean Bad predicate with coefficient-divisibility guards, cert_sound extended, and the 2,816 evaluations reproduced in Lean. The separate root lemma proof skeleton for `a%16=9,b%8=5` was sent to Agent 32 and is also in the latest broadcast.

The short-burst audit with the corrected formula remains: n=5 branch 9 has 15 excluded d residues; n=13 branch 9 has d=6 and22 excluded; no n=1 or n=3 closure. Those exclusions have direct root-row explanations in my previous message.
