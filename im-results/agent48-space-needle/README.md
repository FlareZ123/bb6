# Space Needle: original-source high-level arithmetic and terminal inverse languages

**Research status (6 November 2026):** This dossier studies the unresolved Space Needle six-state two-symbol machine `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`. Its exact source-matched arithmetic is proven, and several infinite synthetic predecessor languages have Lean checks. **No genuine blank-root terminal hit or nonhalting proof has been found.** The research remains intermediate; neither BB(6) nor a new lower bound is determined.

## Source provenance and core map

The original source is Google DeepMind's [Cryptids Space Needle module](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean), pinned to `ced8f9f44f67a167d5ecc03e687b048c67926371`. Its machine-level theorem reduces original blank-tape halting to the iteration of `highLevelNext` starting at `N 1`.

[SpaceNeedleClosed.lean](SpaceNeedleClosed.lean) proves original-source classification of **all** high-level inputs. Let `H(0)=0, H(k+1)=2(H(k)+1)`, `O(q,0)=2q+1, O(q,k+1)=2(O(q,k)+1)`. Then

```
H(k)+2 = 2^(k+1)
O(q,k)+2 = 2^k (2q+3)
scanEven(H(k),b) = none
scanEven(O(q,k),b) = some (N (b+O(q,k)+k+3(q+1)))
```

For `x=d+2`, writing `v=v₂(x)` and odd `u=x/2^v`, the high-level step fails precisely when `u=1`, equivalently `x` is a power of two. Otherwise `u≥3` and the successor counter is

```
d' = d + v + 3(u-1)/2.
```

Every successful call strictly increases `d`. The exact remaining mathematical question is whether the unique sequence from `d₀=1` ever hits a `d=2^K-2`. Original-source CI [41428740035](https://github.com/FlareZ123/bb6/actions/runs/41428740035) succeeded for the core map; the five-source family, exact boundary theorem and fourth-linear bound are source-certified in [manual CI 42296731159](https://github.com/FlareZ123/bb6/actions/runs/42296731159), with only standard axioms, no `sorryAx`. The quartic enumerator source bridge has separate verification; later lemma-specific provenance is tracked in the linked subdocuments.

## Main mathematically verified reductions

| Topic | Strongest established statement | Proof and decisive limitation |
|---|---|---|
| **All-decimal-residue incoming exponents** | For every `a,r,B` with `r<10^a`, terminal exponents `K≥B` exist with `K%10^a=r` and at least one unrestricted source. | [TERMINAL-RESIDUES.md](TERMINAL-RESIDUES.md); arithmetic Lean checked; purely synthetic incoming edges |
| **Exact odd-block acceleration** | For every positive `m` and `t`, `t` consecutive odd high-level calls carry `N(2^t*m-1)` to `N(5^t*m-1)` when the input is well formed. | [ODD-BLOCKS.md](ODD-BLOCKS.md), [source theorem](SpaceNeedleOddBlocksSource.lean); original-source [CI 41931806607](https://github.com/FlareZ123/bb6/actions/runs/41931806607) succeeded |
| **Two-step odd terminal inverse** | Original-source iff for a legal `O(q,v)` feeding one odd intermediate and then `2^K-2`: `2^(K+1)=5*(2^(v+1)+3)*q+15*2^v+5*v+12` for `K>0`. | [TWO-STEP-ODD.md](TWO-STEP-ODD.md), [original-source Lean](NeedleTwoStepOddSource.lean); [CI 41931806607](https://github.com/FlareZ123/bb6/actions/runs/41931806607) passed |
| **Complete positive terminal odd-block lengths** | A `t>0` consecutive-odd feeding path to `N(2^K-2)` is admissible iff `4*5^(t-1)` divides `K`. | [ORDER-5ADIC.md](ORDER-5ADIC.md), [source theorem](FiveAdicOrderSource.lean); pinned original-source [CI 41935571573](https://github.com/FlareZ123/bb6/actions/runs/41935571573) succeeded |
| **New uniform fourth-linear valuation bound** | Every legal terminal feeder satisfies `4v≤K+2`, except the unique `(q,v,K)=(61,6,13)` predecessor. More generally, if `K=3v+3+s`, then `v≤s+5`. | [OFFSET-STRIP.md](OFFSET-STRIP.md), [all-natural Lean proof](OffsetStrip.lean), [source bridge](OffsetStripSource.lean). **Original source CI 42296731159 succeeded** || **Unique sharp boundary terminal feeders** | Under the necessary wall equality `K=3v+3`, the full original-source affine equation has **exactly two** natural solutions, `(q,v,K)=(45,2,9)` and `(214,3,12)`. | [BOUNDARY-EXACT.md](BOUNDARY-EXACT.md), [kernel-checked iff](BoundaryExact.lean), [upstream bridge](BoundaryExactSource.lean). **Original source CI 42296731159 succeeded**; no blank-root exclusion || **Infinite five-source terminal fan-in** | For every `t≥0`, the destination `N(2^K(t)-2)`, where `K(t)=115559872543250362436240044170777864346536+136996046966732361806630100489564981018852*t`, has five distinct source-valid immediate predecessors of shifted valuations `0,3,20,38,83`. | [FIVE-TERMINAL.md](FIVE-TERMINAL.md), [kernel-checked arithmetic](FiveTerminal.lean), [upstream-import bridge](FiveTerminalSource.lean). **Original source CI 42296731159 succeeded** |
| **Fourth-linear exact terminal inverse enumeration** | The full unrestricted list of all immediate terminal feeders at exponent K is obtained by testing valuations 0..floor((K+2)/4), plus the unique K=13 exception. For all q,v,K, list membership is iff the exact source affine equation. | [QUARTIC-ENUMERATION.md](QUARTIC-ENUMERATION.md), [Lean list theorem](NeedleQuarticEnumerate.lean), [original-source bridge](NeedleQuarticEnumerateSource.lean). **Original-source CI 42298248203 passed**, including complete predecessor iff |

The five-source theorem, both boundary/valuation bounds, and the quartic inverse enumerator are now all source-certified in [CI 42296731159](https://github.com/FlareZ123/bb6/actions/runs/42296731159) and [CI 42298248203](https://github.com/FlareZ123/bb6/actions/runs/42298248203). The verified five-source theorem extends Agent 20's earlier original-source *three*-terminal family [CI 42107688083](https://github.com/FlareZ123/bb6/actions/runs/42107688083); that CI is confirmed successful. Agent 20's stronger independent method for arbitrary **nonterminal** synthetic destinations also yields unbounded unrestricted incoming-degree [paper argument](../agent20-needle-coprime/UnboundedFanin.md). These facts are not statements about the genuine blank orbit.

## Evidence, failed proof routes, and remaining obligation

An exact-bigint exploratory forward test from `N 1` checked 30,000 high-level transitions; the counter grew to 28,098 bits without a power-of-two input. A later 300,000-call finite test visited all residues modulo `2^14` of the shifted counter `d+2`. These are **finite computations** whose purpose is to reject simple modulus-only conjectures. Neither implies infinite survival. Independent backward experiments and additional scripts are retained in this directory.

The [complete fourth-linear terminal inverse enumerator](QUARTIC-ENUMERATION.md) now provides a finite, source-certified iff list for every terminal exponent, tightening Agent20's prior cubic list. This is useful for proof-carrying reverse search but has not classified a genuine blank trajectory.

The immediate necessary equation for a terminal feeder `O(q,v)` is

```
2^K=(2^(v+1)+3)q+(3*2^v+v+3).
```

Many unrestricted solutions exist, including entire progressions with multiple feeders. A successful machine decision must distinguish which, if any, such sources actually occur on the deterministic blank-origin orbit. Inverse source-validity, congruence exclusions and synthetic fan-in are insufficient alone. Focus future research on an all-time source-connected blank-orbit invariant, a genuine terminal witness, or a complete inverse reachability argument. Keep experimental notes in `im-results/` until a root-relevant advancement is established.

[Manual original-source verification workflow for the five-source theorem](../../.github/workflows/agent48-space-needle-five.yml) never runs on repository push.
