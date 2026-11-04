# Machine C: exact one-step predecessor count on a second-stopping ray

**Agent 11, 2026-11-04.** Intermediate arithmetic result for the genuine Machine C accelerated section, building on the original-source exact-image theorem in [the section dossier](README.md). The original image biconditionals and the all-depth incoming-fan lower bound have passed unchanged-repository-source Lean CI [41755165300](https://github.com/FlareZ123/bb6/actions/runs/41755165300) and [41757436020](https://github.com/FlareZ123/bb6/actions/runs/41757436020). The **new exact cardinality formula below is a mathematical derivation from those certified biconditionals, with finite independent computation, and has not yet been separately formalized as a Lean cardinality theorem**. It says nothing about reachability from the blank tape.

## The family and exact formula

For each `m ∈ ℕ`, set
```text
B = 3m+4,        D = 4^(m+1) B,
X = 6m+5,        Y = D-6m-6,
v = v₂(B),      B = 2^v U (U odd),
e = 2m+2+v.
```

The target `T_m=(X,Y)` is a true member of the second *stopping-parameter* family: with `j=3m+1` it satisfies
```text
X = 2j+3,     Y+j+3m+5 = 2^(2m+2)(j+3).
```

**Arithmetic claim:** for the original `BB6.Agent46.secNext` map,
```text
#{(a,k) ∈ ℕ² : secNext(a,k)=some(T_m)} = m+1+ceil(v₂(3m+4)/2).
```

This counts **all** immediate section predecessors, including those not visited by the genuine blank-origin orbit. In particular, the fibre has unbounded size even when restricted to true second stopping-parameter targets. The previous [SecondGateFanOriginal.lean](SecondGateFanOriginal.lean) proved only `≥m` for this precise family.

## Exhaustive symbolic classification

As `Y≥10` is even, and `X+Y=D-1` is odd, the complete original-source branch cases for `secNext` leave exactly these possible predecessors.

**Direct high-sector input (always one):**
```text
(a,k) = (D-3, (Y-2)/2).
```
Indeed the branch `a≥2, k>0, 2k≤a` returns `(a-2k,2k+2)`. The low special cases return second coordinates at most seven, and the direct `k=0` branch returns second coordinate two.

**Odd-`a≥3` bounce inputs:** a successful high-sector bounce must have `a` odd: if `a` is even, the odd-`(a-1)` bounce image has even output sum, contradicting `X+Y` odd. For odd `a`, the even-bounce image biconditional, with `Y≥5`, reads
```text
D = 2^n (2a+6) = 2^(n+1)(a+3),
2k+a+7+3n = X+2Y.
```
As `X+2Y` is odd and `a` odd, the second equation forces **odd `n`**. Set `H=D/2^(n+1)`. For each odd `n≥1` for which `H` is even and `H≥6`, the unique source is
```text
a_n = H-3,
k_n = (X+2Y-a_n-7-3n)/2.
```
These inputs satisfy `k_n>0,2k_n>a_n` and the even-bounce converse, so they genuinely return `T_m`. Distinct `n` have strictly different `a_n`.

Writing `D=2^e U`, the allowed depths are:
- `U≥3`: odd `1≤n≤e-2`, giving `m+ceil(v/2)` sources.
- `U=1`: odd `1≤n≤e-4`, giving `m+v/2-1` sources. Here `B=2^v≡1 (mod 3)`, so `v` is even and `e≥4`.

For input `a=0`, the relevant bounce has odd parameter and forces an **even** output sum; its special `k=1` output has second coordinate four. Thus it cannot produce `T_m`.

**Exceptional `a=1,k≥4` input:** its bounce parameter is four, and the high-image equation becomes
```text
D=16·2^n,     2k+11+3n=X+2Y.
```
This exists precisely when `U=1`, with unique `n=e-4` (even) and `k=(X+2Y-11-3n)/2≥4`. It contributes exactly one extra source in the power-of-two case.

Counting the direct source, all odd-`a` high bounce sources and the exceptional `a=1` source gives the claimed `m+1+ceil(v/2)`.

### Elementary feasibility bounds

For the odd-`a` sources, `n≥1` gives `H≤D/4`; `v≤3m+3` implies `n≤5m+3`. Since `4^m≥m+1`,
```text
2k_n-a_n = 2D-2H-6m-8-3n
         ≥ 3D/2-21m-17
         ≥ 6(m+1)(3m+4)-21m-17 > 0.
```
The last inequality holds for `m≥1`; there are no allowed odd-`a` sources at `m=0`. It also ensures `k_n>0`. In the exceptional `a=1` case `n=e-4≤5m+1`, and `2k=2D-6m-18-3n≥2D-21m-21≥11`, hence `k≥4`. The integer and parity conditions follow from `e,v`, the odd depth, and `X+2Y` odd.

## Independent finite cross-check and proof boundary

A separate Python translation of the **literal** `BounceCalc.lean` and `FastSectionDef.lean` branch definitions checked every constructed input for `0≤m<75`, verified all sources were distinct, and matched the formula in every case. An exhaustive enumeration of **all** `a,k` permitted by the independently source-certified mass inequality `a+2k+2≤X+2Y` found exactly the listed sources for `m=0,1,2` (targets `(5,10)`, `(11,100)`, and `(17,622)`). These runs are finite validation and cannot replace the all-natural symbolic classification.

| m | v₂(3m+4) | exact predicted predecessor count |
|---:|---:|---:|
| 0 | 2 | 2 |
| 1 | 0 | 2 |
| 2 | 1 | 4 |
| 3 | 0 | 4 |
| 4 | 4 | 7 |
| 5 | 0 | 6 |
| 20 | 6 | 24 |

**Remaining formal work:** create a Lean theorem identifying the entire original-source fibre with this disjoint arithmetic union, then prove its cardinality. Source correctness of the existing image biconditionals should be reused, without recomputing or replaying the already checked bounce derivation. Any root-reachability consequence would additionally require a blank-orbit obstruction on **every** listed source. None is currently proved.
