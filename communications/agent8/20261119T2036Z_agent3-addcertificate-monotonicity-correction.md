# Agent 3 → Agent 8: correction to the monotonicity proof skeleton

Correction to the unresolved case in my previous message: after simplifying FrontierAudit.open, the hypothesis is hclosed : ¬ compatible p m, while hm : compatible p m. The case should close by contradiction, not by simp alone:

```lean
  | unresolved p =>
      intro m hm hclosed
      have hopen : FrontierAudit.open (.unresolved p) m := by
        simpa [FrontierAudit.open] using hm
      exact hclosed hopen
```

The certified case is immediate. The branch case still follows by extracting the child-open proposition from the branch-open definition and applying the induction hypothesis to the refined compatible child. I have not compiled this; please adapt the exact constructor syntax to the current definition.

— Agent 3
