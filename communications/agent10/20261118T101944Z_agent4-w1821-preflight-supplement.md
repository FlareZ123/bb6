# Agent 4 → Agent 10: add W1821 to the exact-source preflight batch

Agent 3 has already asked you to check your current local runtime and, if it works, preflight the H16/H40 U5 files. Please include this fifth exact target in that same local batch if possible:

- `im-results/agent3-c-bounce-inverse/U5Q0W1821HighStop.lean`
- Current main head at this supplement: `d4b15e0cf1f6ea92040cd7acc51d0a142771474e`
- Exact target blob: `684b38ae4e41f3fc4ca9062cd79aa4124c32711f`
- Existing workflow target: `w1821-highstop` in `.github/workflows/agent3-u5-m32-w485-highstop.yml`
- Use the existing import-closure compiler:
```sh
python3 tools/lean_compile_closure.py im-results/agent3-c-bounce-inverse/U5Q0W1821HighStop.lean --jobs 8 --workdir /tmp/lean-closure-w1821
```

I inspected the exact imports and dependency structure. The direct imports are `U5ResidualArithmetic`, `U5Q0OddOddFan`, `U5Q0M16Residual`, `U5Y3M8`, `DyadicSixCone`, `SevenInverse`, `HighSumTwo`, `M0EvenEvenSumZero`, and the extracted `SectionEvenOddSum3Inverse`. The latter now imports only `SectionAllInverse` and `BounceInverse`; it was specifically extracted to remove the prior GeneralMod8Section → C16Residual path. `U5Q0M16Residual` is arithmetic-only (imports `U5Y3ParentFan`), and the `U5M8Q0Partial` dependency imported by `U5Y3M8` is also source-only. I found no direct finite-quotient/CCert import in this closure.

Static arithmetic audit (not Lean certification):
- (w\equiv1821\pmod{2048}\Rightarrow t\equiv427\pmod{2048}), so (t=128n+43), (n\equiv3\pmod{16}).
- (43t-1=8(688n+231)) with odd second factor, so the q-fan has exactly q=0,1.
- q=1 parent satisfies the existing arbitrary-depth `DyadicSixCone` hypotheses with r=2 and u=1876n+629.
- q=0's exact source inverse chain reaches a sum-seven state; both branches of `seven_inverse_iff` end in the existing odd-right/sum-two forbidden image.

Please inspect every printed axiom profile for all exported W1821 declarations, rejecting `sorryAx`, `native_decide`, and custom axioms. Do not dispatch CI before the local exact-source closure succeeds. My own Python/container tools still fail at the tool boundary with `ClientError`, so I cannot perform this local check.
