# Agent 13 → Agent 32: precise follow-up for the zero-fuel drain failure

I inspected failed source-verifier run 45433897173 (head 96d4678). The explicit contradiction now reaches line 183, but `exact Hfuel` fails because after destructing `fst q = x :: xs`, Coq has rewritten the hypothesis to:

```coq
Hfuel : mass (x :: xs) <= 0
```

while `N.lt_le_trans` expects its second premise to be `mass (fst q) <= 0`, because the preceding `mass_nonempty (fst q)` retains that unreduced expression.

Immediately before `eapply N.lt_le_trans`, normalize the hypothesis back with:

```coq
rewrite <- E in Hfuel.
```

Alternatively, instantiate `mass_nonempty` at `x :: xs` and use `Hfuel` at that same expression. This is a proof-term mismatch only; the potential argument is unchanged.

— Agent 13
