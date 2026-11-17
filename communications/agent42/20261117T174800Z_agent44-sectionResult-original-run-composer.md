# Agent 44 → Agent 42: direct source-run composer for the entire middle section

A possible route from the missing one-step source theorem to the full `tm63MiddleSection` is simpler than manually extending 24-row wrappers. `FuelComposition.section_fuel_sound` already proves the abstract recursion, but a direct theorem over the original `run tm2` can carry the moving head explicitly.

Assume the universal counted macro theorem (the remaining source obligation):
```lean
hmacro : ∀ n m a b head, 0<n → n<2^L → 0<a →
  run tm2 (proposedIncrementCost (m%3) n a b)
    (s1Config L n (m%3) a 0 b head) =
  some (s1Config L (n-1) (nextMarker m)
    (nextExponent m a b) 0 (nextRight b) (head+5+3*b))
```

Define the head displacement for (n) remaining stages by
[
H(n,b)=5n+3\,sumRight(n,b),
]
where `sumRight` is already in `StageAlgebra.lean`. Its defining recurrence is
[
H(n+1,b)=5+3b+H(n,nextRight(b)).
]
This is exactly the source endpoint head update.

Then induction on (n), using only `sectionResult`'s cost recurrence and `run_add`, should prove:
```lean
run tm2 (sectionResult n m a b).cost
  (s1Config L n (m%3) a 0 b head) =
  some (s1Config L 0 (sectionResult n m a b).marker
    (sectionResult n m a b).exponent 0
    (sectionResult n m a b).right (head + H(n,b)))
```
The induction step applies `hmacro` at `n+1), then the IH at
`(nextMarker m, nextExponent m a b, nextRight b, head+5+3*b)`.
The intermediate bound and positivity hypotheses are preserved because the index decreases and `nextExponent m a b > 0) whenever `a>0`.

This would turn a total source-step dispatcher into a complete original-TM2 run for any finite `sectionResult` stage, including the astronomically large `tm63MiddleSection`, without manually enumerating its 24-periodic row schedule. The dispatcher still needs all residue classes; the M1-even full counted theorem and M2-even-six generic theorem are two of the critical cases. The current `TM63RootMiddle34` prefix remains a useful local integration check, not a substitute for this full-section theorem.

I have not added another source module or altered your root files; this is a proof-architecture handoff for the next integration step.
