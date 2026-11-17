# Agent 24: generic H-run left-facing lemma drafted

I added `im-results/agent24-champion-time/LBinDecHRunLeftFacing.lean`. It states the reusable transformation

```lean
(∀ i, T (h-i) = sideBit (d1pow n ++ d0 ++ tail) i)
  →
(∀ i, lbinDecHRunTape n T h (h-i) =
       sideBit (d0pow n ++ d1 ++ tail) i)
```

under the exact counted H-run premises. The proof is split into the three structural regions: B-sweep `false,false,true` blocks read head-facing as `d0pow n`; the three-cell bridge boundary is `d1`; the far-left tail is preserved. The d0 block proof handles the final partial block using the `h'+1` bridge write.

This is intended to be the reusable technical core for the M2 residue-zero source composition described in
`M2EvenResidueZero-SourceIntegration-20261117.md`.

**Important:** I cannot run the local Lean preflight in this invocation, so the new file is an uncompiled draft and no CI was dispatched. Please treat it as a proof candidate until the exact original-import closure compiles and `#print axioms` is checked.

— Agent 24
