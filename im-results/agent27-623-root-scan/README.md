# Source-faithful #623 root gap/scale scan

This directory contains a dependency-free JavaScript BigInt replay of the high-level section map for the six-state machine

```text
1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA
```

It is a finite computational diagnostic, not a nonhalting proof.

## Reproduction

Requires Node.js with BigInt support:

```bash
node RootGapScaleScan.js 20000
```

The script is pinned to `google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b`, file `BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean`. It implements the source equations for `evalA`, `drainB`, and `highLevelNext) using BigInt. Crucially, the `r=1,a>0` case of `evalA` recursively continues with `A(a-1,j,m+2j+3)`; it must not return the intermediate tuple as a completed `D3) state.

## 20,000-transition result

The 20,000-step run in the V8 runtime used for this invocation produced:

| Diagnostic | Exact/observed result |
|---|---:|
| transitions | 20,000 |
| checked indices | 9 through 19,999 |
| side-selection mismatches | 0 |
| zero ratio-four gaps | 0 |
| minimum root gap slack | 65 |
| minimum-slack state | index 14, `D(314,385)`, `h=71,m=314` |
| minimum `|g|/m` | `log2 = -12.960451552003178`, index 6,899 |
| minimum `g^2/m` | `4096/235`, `log2 = 4.123483053435001`, index 16 |
| maximum `|eg|/ternaryDigits(m)` | `102/4 = 25.5`, `log2 = 4.672425341971495`, index 11 |
| maximum `|em|/ternaryDigits(m)` | `24/4 = 6`, `log2 = 2.584962500721156`, index 11 |

Here, for a state (D(a,d)),
- (m=min(a,d));
- (g=a-4d) when (age d), and (g=d-4a) otherwise;
- ((g',m')=(g-9m,3m)) when (g>0), and ((g',m')=(-4g-9m,3m+g)) otherwise;
- (e_g=g_{mathrm{actual}}'-g') and (e_m=m_{mathrm{actual}}'-m');
- (mathrm{ternaryDigits}(m)) is the base-3 digit count of (m).

The minimum-slack calculation is exact: for (m>0), (lceillog_3(2m+1)ceil) equals the number of base-3 digits of (2m), so the reported slack is
[
|a-d|-lceillog_3(2m+1)ceil.
]
At index 14 this is (71-6=65).

The first 20 root states emitted by the script are
[
egin{aligned}
&D(0,7),D(6,14),D(6,31),D(26,26),D(2,83),D(84,10),\
&D(74,38),D(30,138),D(108,101),D(2,321),D(322,10),\
&D(312,38),D(268,138),D(122,438),D(314,385),D(74,950),\
&D(876,235),D(632,735),D(104,1914),D(1808,329).
end{aligned}
]

## Relationship to the older C++ diagnostic

The older `im-results/agent8-623-inverse/root_gap_scale_scan.cpp` has a source mismatch in its `evalA` implementation: its `r=1,a>0` branch returns instead of continuing the recursive `A)-evaluation. Its current checked-in code therefore cannot produce the 20,000-step output above. The JavaScript replay independently reproduces the historical numeric metrics using the pinned Lean equations; the old C++ file still needs repair before its own output can be trusted.

## Interpretation and limitations

The 20,000-step result is empirical evidence only. In particular:
- zero mismatches over a finite prefix does not prove the branch-selection rule for all future states;
- the observed 65-slack inequality is not forward-invariant for arbitrary states (for example, `D(2,69) -> D(70,10)` satisfies it at the input but not at the output);
- no all-time root-history invariant has been established;
- this does not prove that the machine is nonhalting and does not resolve any BB(6) holdout.

The useful next mathematical task is still to derive a root-specific inductive/cocycle invariant that keeps the blank-root orbit in the source-certified `newAffineCone) after its finite entry prefix.
