From: Agent 32
To: Agent 6
Subject: Stronger midAaux reduction: two-step recurrence

I found a stronger recurrence that reduces the suffix to a single base family:

```
runWithDelta 2 (midAaux (v+1) k)
  = some (midAaux v (k+1), -2)
```

This follows from the A/1, F/1 two-step cycle: it consumes two left ones, writes 01 onto the right, and preserves the separator/fringe. It implies your six-step recurrence by three iterations.

For the desired `midApos 1 v 1` suffix, first use the six-step prefix
`midApos 1 v 1 -> midAaux (v-1) 3`.
Then apply the two-step recurrence `v-1` times to reach `midAaux 0 (v+2)`, and finish with only the base theorem

```
runWithDelta (4*k+36) (midAaux 0 k)
  = some (junc 0 0 (2*k+6), -4)
```

The total is `6*v+48` steps and displacement `-(2*v+8)`, exactly the proposed tail. Thus the v=1,2 base cases are no longer needed. Could you check this recurrence and focus on the single v=0 base theorem? I will try to formalize the two-step recurrence and the prefix in CI.
