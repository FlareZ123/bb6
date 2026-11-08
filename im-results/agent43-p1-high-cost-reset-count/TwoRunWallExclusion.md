# P1: unbounded depth-two runs with a single shallow inverse transition

**Current evidence (8 November 2026).** A new all-natural Lean 4.36.0-rc2 theorem excludes the exact shifted wall for an inverse-word grammar consisting of an arbitrary initial depth-two run, **one** depth-zero or depth-one edge, and an arbitrary final depth-two run. The proof is fully kernel-checked for its stated **arithmetic premises** and has no `sorryAx`. Its connection to the unmodified P1 `inverseAt` and `CountCone` is at the source-identity derivation stage; an original-source integrated Lean wrapper has **not yet been compiled**. It is an intermediate necessary-word exclusion. P1 halting and BB(6) remain open.

## The affine cocycle

Let `P=2^n`, `W=b+4m+4n+20` and `B=m+n+6`. Original-source P1 energy identities, previously verified by Agent50, give the depth-two transition

```
8 W' = W + 84 P + 16 B,       B'=B+3.
```

Define `I(P,W,B)=49W-588P-112B+384`. One depth-two transition satisfies `I(P,W',B')=I(P,W,B)/8`. Hence every (finite, unbounded-length) depth-two run of length `r` satisfies `I_before=8^r I_after`, proved in [TwoRunModel.lean](TwoRunModel.lean).

The same source identities imply the following **single shallow edge** formulas, with `B` the cost coordinate immediately before the edge:

```
depth 0: 2 W' = W + 4 B - 8,          B'=B+1
depth 1: 4 W' = W + 28 P + 8 B - 8,   B'=B+2.
```

The root is `(b,d,m)=(14P-2n-16,3,0)`, with `W_root=14P+2n+4`, `B_root=n+6`, and `I_root=98P-14n-92`.

## Uniform all-n result for one shallow edge

Consider the entire inverse-depth grammar `(2)^s · (0|1) · (2)^r`, for **any** naturals `s,r`, from the above root. The endpoint exact shifted wall is `W_end=12P`.

The prefix depth-two defect condition gives `8^s | (98P-14n-92)`. Since `0<14n+92<2^n` for `n>=14`, the dyadic remainder lemma first forces `3s<=n`. Consequently `8^s|P` and `8^s|(14n+92)`. Write

```
q=8^s,   P=q*p,   14n+92=q*d.
```

Using the unique shallow edge and the final depth-two defect relation, a genuine exact-wall hit would require one of the following **integer equations**:

```
depth 0: (588*q-98)*p =
  (224*n+672*s+672*r+800)*8^r + (84*n+252*s+272-d)

depth 1: (392*q-98)*p =
  (448*n+1344*s+1344*r+2048)*8^r + (56*n+168*s+200-d).
```

**Theorem:** Neither equality has a solution in natural `n,s,r,p,d` with `n>=14`, `8^s*p=2^n` and `8^s*d=14n+92`. The Lean declarations `no_zero_middle_all` and `no_one_middle_all` in [OneShallowFiniteBridge.lean](OneShallowFiniteBridge.lean) prove this without a reset-count, suffix-length, or cost cutoff.

### Symbolic proof for n>=28

If `K*2^e=A*8^r+R` with `0<R<2^e`, modular divisibility forces `3r<=e` and `8^r<=R`. Apply this at `e=n-3s`. The divisibility `q|(14n+92)` bounds `q<=21(n+2)`; the remainder bound yields `R<2^{n-3s}`. Therefore `3(s+r)<=n`. Substituting into either wall equation gives a polynomial upper bound contradicting the fully proved all-natural inequality

```
8192*(n+2)^3 < 2^n       (n>=28).
```

All inequalities and both shallow-sector contradictions appear in [CubicGap.lean](CubicGap.lean) and [OneShallowLarge.lean](OneShallowLarge.lean); their Lean axiom reports contain only standard axioms.

### Complete finite range 14<=n<=27

The same integer equations imply `s<=2` since `8^s|(14n+92)<=470<512`, and `r<=12` since `8^13>588*2^27` bounds any possible right-hand product. [OneShallowFinite.lean](OneShallowFinite.lean) checks all `n∈[14,27], s∈[0,2],r∈[0,12]` via ordinary kernel `decide` on exact divisions, powers and equality. This finite Boolean theorem has **no axioms**. [OneShallowFiniteBridge.lean](OneShallowFiniteBridge.lean) proves the authentic quantified arithmetic assumptions imply those finite checks, and combines the small and large regimes. The public all-n theorems use `[propext, Classical.choice, Quot.sound]` only.

## Earlier direct-shallow result

For `s=0`, the wall equations simplify to

```
245*2^n = (112*n+336*r+400)*8^r+(35*n+90)
147*2^n = (224*n+672*r+1024)*8^r+(21*n+54).
```

[DyadicGap.lean](DyadicGap.lean), [TwoRunModel.lean](TwoRunModel.lean), and [TwoRunBridge.lean](TwoRunBridge.lean) directly prove these two all-n original-root **arithmetic model** exclusions without `sorryAx`. The stronger one-shallow theorem includes all such equations and more.

## Verification, context and next decisive action

Compile files in this order using Lean 4.36.0-rc2 with import path set to their folder: `DyadicGap`, `TwoRunModel`, `TwoRunBridge`, `CubicGap`, `OneShallowLarge`, `OneShallowFinite`, and `OneShallowFiniteBridge`. Local compilation of each completed successfully; `#print axioms` on `no_zero_middle_all` and `no_one_middle_all` showed `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. No full original-source CI was invoked for this new chain.

**Open integration step:** Formally lift the original `inverseAt` depth-zero/one/two formulas to the affine `TwoRun` model and derive both quantified wall equations from a `CountCone` history of shape `2^s(0|1)2^r`. The original-source cocycle and mass equations are available in [Agent50's source energy modules](../agent50-p1-subwall/RightFiveEnergyStep.lean), and the root mass is in [DepthIndexedResetFloor.lean](DepthIndexedResetFloor.lean). Until this bridge is Lean checked, avoid labeling the new theorem original-source-certified. Earlier [Agent50's all-count logarithmic reset-density theorem](../agent50-p1-subwall/README.md) has successful original-source CI [42520350507](https://github.com/FlareZ123/bb6/actions/runs/42520350507), but it is a necessary lower bound rather than a decisive wall exclusion. These results are complementary; external novelty remains to be reviewed. Full P1 closure requires handling words with multiple shallow edges, arbitrary high-depth excursions, and authentic blank-root implications.
