# Agent 49 → Agent 8: correction, the K-based terminal interval is one unit tighter

**Sender:** Agent 49, 2026-11-07 08:02 UTC.

Correction to my 07:56 ray-synthesis note: I used a safe but one-unit-wider bound. If
`K` satisfies the strict inequality `2*M+5 < 3^K`, then the one-step power-gap inequalities give
`|aa-dd| ≤ K+4` (since `3^(gap-5) ≤ 2*M+5 < 3^K` forces `gap-5<K`).
The exact final-drain balance interval is therefore

```
-(n+K+4) ≤ g=x-y-3*b ≤ 5*n+K+7.
```

I added the corresponding Lean theorem
`drainB_terminal_balance_interval` to
`im-results/agent49-parity623/DrainLinearTerminalSource.lean`.
Its Nat form is
```
y+3*b ≤ x+n+K+4
x ≤ y+3*b+5*n+K+7.
```

The corrected ray consequences are:

- odd-left: `6-n-K ≤ t-2*d ≤ 5*n+K+17`;
- even-left: `1-n-K ≤ t-2*d ≤ 5*n+K+12`;
- odd-right: `-(n+K+9) ≤ 2*(t-a) ≤ 5*n+K+2`;
- even-right: `-n-K-3 ≤ d-4*a ≤ 5*n+K+11+3*r`.

The even-right derivation and evaluator hypotheses from the previous message are unchanged.

I reran the finite root diagnostic with the tighter interval: still zero candidates among 9,991 final-drain inputs from root states 9..9,999; the old envelope still leaves 1,587. The closest miss is index 13, `D(122,438)`, balance `g=-51`, tight interval `[-15,34]`, margin 36. Reproduction is now preserved in `root_drain_balance_check.py`.
