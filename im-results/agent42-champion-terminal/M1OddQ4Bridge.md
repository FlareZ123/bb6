# M1,n=3 odd q4 bridge (intermediate)

**Status:** the 26-step finite bridge is kernel-checked locally with Lean 4.36.0-rc2, and a repository source lemma has been added. The full parametric reset stage is not yet formally proved.

## Finite bridge

Source file: [M1OddQ4Bridge.lean](M1OddQ4Bridge.lean)

The exact finite-list certificate is

```lean
fRun tm2 26 ⟨3,0,[-4,-1]⟩ =
  some ⟨4,2,[1,-1,-4,-5,-6]⟩
```

Every pre-step head lies in the interval `[-6,1]`. The output list order is significant: `fMove` prepends newly written one-cells, so the exact end list is `[1,-1,-4,-5,-6]`.

This bridge includes the state-5 zero-cell write at relative head `+1`, ending in state 4 at relative head `+2`. After a counted left sweep of `N=3a+1` cells, the input frame `[-6,1]` is exactly state 3/head 0 with marks `[-4,-1]`, for `a>0). The following E-scan has length `3a-1`, from relative head `+2` back to the original head.

Thus the proposed pre-Q4 prefix length is

```
3(3a+1) + 26 + (3a-1) = 28 + 12a.
```

## Candidate Q4 cut

The deterministic simulator gives the following candidate q4 cut at state 4 and the original head:

- left-facing word: `[true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec 3 2 ++ lh`;
- right-facing word: the usual `q4RightFacing b`.

The generic q4 suffix then runs `39+3b` steps to the S1(3,2,0,...) pre-drain state; the counted drain completes the proposed `(m,n)=(1,3)` increment. The full reset-plus-drain replay and exact intermediate tape matched for `1 ≤ a ≤ 4`, `0 ≤ b ≤ 4` (20 parameter pairs). This is bounded computational evidence, not a proof of the parametric cut identities.

## Next formal obligations

1. Prove the post-sweep input-frame match on `[-6,1]`.
2. Transport the 26-step bridge through `frameAt`.
3. Prove the E-scan cells and exact q4 left/right cut shapes.
4. Prove the marker-0, n=2 q4 suffix left carry identity and compose the generic suffix plus counted drain.
5. Extend `TM63M0M2RootComposition.lean` to factor this `(1,3)` stage from the residual and start the next conditional theorem at S1(3,2,0,...).

The existing manual-only source workflow now compiles the finite bridge after `ChampionRootBridge`, with a transitive `sorryAx` gate. It has not been dispatched.
