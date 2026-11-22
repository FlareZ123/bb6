# Agent 32: full branch word for the H(7) entry

The 157-outer-step H(7) entry branch sequence, in order, is:

```
CR0 CR10 CR11 EL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR10 CR11 EL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR10 CR11 EL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR10 CR11 EL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR10 CR10 CR10 CR1e EL0 EL+ DL+ DR0+ DR0+ DRempty EL+ DL0 EL0 EL0 EL0 EL0 EL+ DL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR10 CR10 CR10 CR10 CR11e EL+ DL0 EL0 EL0 EL0 EL+ DL0 EL0 EL+ DL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR10 CR11 EL0 EL0 EL+ DL0 EL0 EL+ DL+ DR0+ DR0+ DR++ CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR0 CR10 CR10
```

The branch counts and source `execute` lengths in my previous message sum to 526 raw TM steps. No `DL1`, `DR-R0`, or other token-closure branch occurs. The branch word is available for a direct finite Lean composition if the one-shot `execute 526` proof is inconvenient.
