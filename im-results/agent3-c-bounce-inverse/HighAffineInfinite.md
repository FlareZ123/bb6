# An infinite Machine C high-stopping family excluded by three exact backward returns

**Agent 3, 2026-11-03 18:55 UTC.** [HighAffineInfinite.lean](./HighAffineInfinite.lean) contains a kernel-certified all-parameter theorem. **Original unmodified source [CI run 41698364955](https://github.com/FlareZ123/bb6/actions/runs/41698364955) completed successfully at 18:58 UTC**. The job compiled unchanged source dependencies and printed only [propext, Classical.choice, Quot.sound] for high_halt_affine_three_unreachable. The immediately preceding full-filter [CI 41697759547](https://github.com/FlareZ123/bb6/actions/runs/41697759547) **succeeded** on unchanged original source, with standard Lean axioms only. The all-parameter exclusion is now original-source-certified; its external novelty is still subject to review.

## Uniform theorem

For **all** natural `j,m,k,time` satisfying

```
m >= 6
m % 4 = 2
(j + 127*m) % 128 = 87
k + j + 3*m + 5 = 2^(2*m+2)*(j+3)
```

the proof derives

```
run secNext time (some (5,1)) != some (2*j+3,k).
```

The final equation is the source-certified full **higher stopping family** from Agent 15, [SectionParam.lean](../agent15-c-halting/SectionParam.lean). Consequently the class consists of authentic Machine C section stopping inputs excluded **for all genuine blank-orbit times**, not merely abstract candidate coordinates. This family is distinct from earlier source-proved m%4=2 family `(j+m)%256=222` and the m%4=0 second wedge.

## Proof and source lineage

Write the stopping target as `(x,y)=(2j+3,k)`. The exact first inverse (Agent15 affine return for y even) is

```
A=(x+y-2,(y-2)/2).
```

Then the exact odd/odd low-valuation inverse, proved in [OddOddLowVal.lean](./OddOddLowVal.lean), is

```
B=((A.first+A.second-4)/2,
   (A.first+3*A.second-10)/4).
```

Finally the exact even/odd seven-sector inverse, proved in [OddSevenOrbit.lean](./OddSevenOrbit.lean), is

```
C=((B.first+B.second-5)/2,
   (B.first+3*B.second-9)/4).
```

For every parameter in the theorem, formal `omega` arithmetic shows that all three exact inverse guards hold, each predecessor exists in the **original** total Machine C section, and `C.second` is odd≥5 with `(C.first+C.second)%4=2`. The latter contradicts the [genuine blank-section image invariant](../agent3-c-odd-image/Agent3CImage.lean) that every positive-time return with odd right≥5 has sum **0 or 3 mod4**. The initial blank section (5,1) has right counter below5. The proof uses no finite simulation, abstract quotient transitions, or induction over an arbitrary finite number of steps.

Power growth and modular arithmetic are formalized internally: `128∣2^(2m+2)`, the stopping equation gives `(k+j+3m+5)%128=0`, and an earlier separately proved exponential bound yields `k>=100`. These suffice for all three strict source return guards and the final parity contradiction. `#print axioms high_halt_affine_three_unreachable` is included for the original-source CI.

## Concrete example and quotient comparison

At `m=6, j=93`, the stopping counter is `k=1,572,748` and target `(189,1,572,748)`. Its three exact source predecessors normalize to `(1,081,329,1,032,169)`, whose right counter is odd and sum congruent to two modulo four. The general full Boolean filter independently kernel-certifies this example by `decide +kernel` in [FullForcedFilter.lean](./FullForcedFilter.lean), source-verified in successful CI 41697759547.

The source-faithful B8/M32 finite graph independently reproduced 31,570 reachable abstract states and 189,834 edges. This concrete target projects to **(29,12,0)**, which is **present** in its reached set. Across bounded test values m∈[3,35], j∈[0,255], this new congruence sector contributed 16 additional high stopping targets admitted by B8/M32 but excluded by the sound three-sector forced inverse filter. Thus direct abstract target absence in that particular quotient is insufficient for these cases. The quotient comparison is computational and does not enter the theorem.

Even if original-source CI succeeds, this does **not** resolve Machine C nonhalting or BB(6): infinitely many other high and low stopping parameters remain. Assess overlap with other agents' deeper source-checked M16/M32/mixed96 proofs before calling the result academically new or promoting out of `im-results/`. Investigate whether affine and dyadic predecessor extensions can produce a global disjoint exhaustion of the remaining stopping locus.

## Independent mixed96 reachability audit (2026-11-03, Agent 3 successor)

[Mixed96AffineAudit.cpp](./Mixed96AffineAudit.cpp) independently reproduces Agent41's [mixed96.cpp](../agent41-mixed96/mixed96.cpp) using the exact published nextC branch transcription and its same eight-representative abstract-edge semantics. In a locally compiled C++17 test, the BFS counted exactly **260,672 reachable states and 2,022,544 outgoing representative edges**, matching Agent41. The code checks all 288 parameter residue pairs modulo 384 satisfying the new source-certified family and found **12 distinct projected target cells, all abstract-reachable**. The longest shortest abstract BFS path among these cells was 450 edges. This is a finite, independently replicated quotient experiment; the quoted source theorem, rather than this experiment, supplies true blank nonreachability.

The complete set of reached projections (a mod96,k mod96,c=0) is:

- (5,28), (21,28), (37,28), (53,28), (69,28), (85,28);
- (13,76), (29,76), (45,76), (61,76), (77,76), (93,76).

This 12-cell coverage is not merely a sample extrapolation. The stopping equation at m>=6 yields 2^(2m+2)≡64 (mod96), hence k≡63j−3m+187 (mod96). Since j−m≡87 (mod128) and 63×128 is divisible by 96, k≡60m+4 (mod96). Writing m=4r+2 gives k≡48r+28 (mod96). Simultaneously 2j+3≡5 (mod16) for even r, or 13 (mod16) for odd r. These are precisely the twelve cells above, and all occur for admissible residues. The independent BFS confirms membership of all twelve, without supplying true-machine blank reachability.

**Implication:** direct nonmembership in Agent41's mixed96 quotient, even if its full forward closure were separately Lean-certified, cannot prove this family unreachable. The source-exact three-step inverse obstruction distinguishes genuine blank reachability beyond this specific abstraction. This is a **relative strength comparison**, not proof of external novelty over all existing mathematical methods or a Machine C/BB(6) decision. The present finding remains in im-results/ for adversarial novelty review.
