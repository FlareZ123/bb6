# Possible universal power-leaf band for the unresolved P1 n≡2(mod16) sector

**Status: computational hypothesis ONLY.** This file documents a falsifiable candidate from finite exact-integer predecessor exploration; it is not a proof of unreachability and is explicitly excluded from `results/`.

## Hypothesis and why it would matter

For each q≥1 set `u=7*2^(16q)-4q-3`. Start backward exploration at both exact Agent45 feeder pairs L0=(4u-4,4u+9) and L1=(6u-2,2u+5). Repeatedly use **all** true positive G inverse ancestors on every positive-odd hub (b,d), where d odd, b≥8 and b%4=0. To every inverse ancestor `GAncestor b d k c` associate its preceding even-left feeder pair `(x,y)=(2k-4,c+4)`. Terminal branches with `x%4=2` contradict the source global reachable even-left mod4 condition. Branches with positive even right y are handled by the global `x+12=14*2^j` necessary condition.

**Candidate band:** every even-right terminal feeder pair `(x,y)` from every such odd-only inverse chain satisfies

```
4*u < x+12 < 8*u.
```

If this were universally true **and** all exceptional c=1 source branches were excluded, then a direct source proof would exclude *all* remaining n=16q+2 critical targets: since u=7*2^(16q)-4q-3, the desired interval lies strictly between adjacent 14-power scales for sufficiently large q after correcting the small 4q offset. More precisely, the necessary power gap actually needed is the stronger `28*2^(16q)<x+12<56*2^(16q)`; a plain `4u<x+12<8u` alone does **not** imply these strict bounds because `4u=28*2^(16q)-16q-12` and `8u=56*2^(16q)-32q-24`. Therefore the candidate as written is **insufficient on its own**, and one must either strengthen the margin by `O(q)` or handle the narrow endpoint strips separately. This distinction is important for any proposed closure theorem.

The existing completed all-q n≡2,50(mod64) Lean proof uses a much stronger 28/56-power interval valid at its 24 explicit leaves. Other q classes generate highly variable, unbounded-looking branching depth. The proposed whole-cone band is meant as an all-depth *research target*, not an already-established invariant.

## Reproducible empirical test and its limits

`odd_cone_band_scan.py` uses arbitrary-precision exact integers and independently implements Agent47's explicit `inverseAt` recurrence. It checks every generated terminal even-positive right branch and detects a potentially exceptional source counter c=1 by `d+b/2+3` being a power of two at least four. With `--max-q 500 --max-nodes 10000`, executed on 2026-11-02:

- **487** q indices fully exhausted their checked inverse cones.
- **13** hit the 10,000-hub cap and remain incomplete: q=38,101,129,146,189,273,294,301,342,346,358,389,498.
- **Zero** examined even-right terminal leaves violated `4u < x+12 < 8u` and no exceptional power-of-two shifted-output nodes were observed.

These are finite sample outputs, do not imply a universal result, and do not prove the generalized scanner captures the entire blank-run halting question without the Lean source bridge. The written source is auditably small and uses exact calculations; any future hypothesis should first be falsified on much larger and arithmetic-adversarial q.

## Exact structural facts already proved in Lean

In `MassInverse.lean`, `InverseIff.lean`, `OddConeMass.lean`, `OddConeCoordinates.lean`, `OddShift.lean`, all originally source compiled with standard axioms in [CI 41461096964](https://github.com/FlareZ123/bb6/actions/runs/41461096964), the complete inverse relation for odd-positive output has exact equations

```
d+b/2+3=2^t*(c+3)
2*k+c+2*t+1+c%2=b+d.
```

For the odd-only predecessor-chain cumulative inverse cost m, root sum S0, and shifted s=d+b/2+3, the pair (s,m) determines both counters:

```
b+2s+4m=2S0+6
d+S0+6=2s+2m
```

and every inverse depth-t edge obeys `2^(t+1)*(s'+m')=2^t*(S0+7)+s`. This may enable a uniform 2-adic/rank inequality that protects the band even for arbitrarily deep synthetic chains. The precise test is whether there exists a genuine odd-cone chain whose terminal feeder is in the narrow gaps near 28 and 56 powers or outside the candidate band. All such counterexamples would invalidate straightforward closure strategies.

No independent conclusion about BB(6) or machine nonhalting follows.
