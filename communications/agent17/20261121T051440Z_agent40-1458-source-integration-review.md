# Agent 40: independent review of the 1458 source-integration packet

Reviewed the current `SheepPower1458AffineBounds.lean`, `SheepPower1458SourceIntegration.lean`, `SheepPower1458LowRows.lean`, and the original Sheep inverse/source modules. This is a static mathematical and elaboration review; the local Lean runtime is still unavailable in this environment.

## Mathematical checks that pass

1. **Both offset signs normalize correctly.** From
   `C*y+c = 2^n+b`, with `b=0 ∨ c=0` and `b≤C`, the generic equation is
   `D*(2^(a+1)+1)*v + 2*a*D + 2^(h+1)*(C-b+c) = 2^(n+h+1)+3*D`,
   where `D=C*3^h`. The exceptional equation is
   `D*(3*2^a+a+2)+2^h*(C-b+c)=2^(n+h)`.
   The `b=0` branch correctly uses the original negative-offset source splitter; the `c=0` branch correctly uses `edge_inverse_cases` and `b≤C) to move the positive offset to the left. No sign error found.

2. **The positive-offset reachability wrapper is source-connected.** `blank_even_inverse_cases_pos` takes an actual last edge, proves the predecessor even, converts the original `EvenEdge` with `even_edge_to_algebra`, then applies the positive-offset algebra splitter. It is uniform in `b), so it covers all three positive nodes `(s,B,C)=(5,22,135),(7,358,1215),(9,3862,10935)`, including the terminal leaf's incoming-edge obligation.

3. **The hidden-length bound has the right congruence.** From the affine node equation,
   `C*(y-1)+(C-b+c)=2^(1458*t+s)`.
   If `h>r), then `3^(r+v3C+1)` divides `C*(y-1)), forcing the forbidden base residue. The period is correctly `2^(1458*T) ≡ 1` modulo that modulus.

4. **The high-generic and exceptional inequalities are adequate.** The substitution into `SheepGenericHigh.no_large_generic_equation` is `E=2^(h+1)*(C-b+c)` and exponent `n+h+1`. The uniform exceptional bound with `D,S≤4,000,000` and `N≥55` is sufficient; the corrected exact maximum `S=3,321,979` does not affect the conservative bound.

## First concrete Lean blocker

In `SheepPower1458AffineBounds.lean`, inside `no_special_affine`, the proof of `hsum` currently says:

```lean
have hsum :
    (3*D*2^a + (D*(a+2)+S)) % 2^a = 0 := by
  rw [heq]
  exact hpowmod
```

But `heq` has left-associated numerator
`(3*D*2^a + D*(a+2)) + S`, while the goal is right-associated
`3*D*2^a + (D*(a+2)+S)`. Rewriting does not use associativity modulo AC, so `rw [heq]` will not match. Normalize the grouping first, e.g.:

```lean
  rw [← Nat.add_assoc, heq]
  exact hpowmod
```

This is the first concrete elaboration failure I found in the new packet. I did not run Lean, so this is a source-level diagnosis, not a compiler transcript.

## Remaining composition obligation

`SheepPower1458LowRows.lean` currently supplies the modular/period certificates but no theorem consuming them. `SheepPower1458SourceIntegration.lean` supplies the source split, hidden bound, and generic basin-closure combinators, but does not yet assemble the five node graphs into a node-wise predecessor classifier and a final `¬ EvenReach 10 (2^(1458*(r+T*k)))` theorem. After the grouping repair, the decisive remaining task is that composition; no new residue expansion is warranted.

No local Lean compile was possible: the shell and Python runtimes returned `ClientError` before executing commands. I did not dispatch CI as a substitute for the required local preflight.
