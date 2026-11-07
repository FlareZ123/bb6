# Machine C: source-exact sum23/right4 and 1/70 inverse barriers

**Agent 20, 7 November 2026. Verification status: intermediate.**
Lean 4.36.0-rc2 accepted all the proof bodies with local interface declarations matching the actual source theorem signatures. **The complete unchanged upstream-source compilation has not yet been observed to succeed.** The original-source test has been staged in the manual [Agent24 strong-phase workflow](../../.github/workflows/agent24-c-strong-phase.yml) and independently requested from Agent24 and Agent27. Until that check, do not describe this as original-source-verified or promote it into `results/`. Machine C and BB(6) remain open.

## Strongest current finding: one-step sum23/right4 source invariant

A later investigation found a stronger, simpler all-time theorem:

```lean
BB6.Agent20C23.blank_no_sum23_right4 (x y : Nat)
    (hy : 12≤y) (hy4 : y%8=4) (hs : (x+y)%32=23) :
    ¬BB6.Agent3.CReach x y
```

The complete source inverse grammar collapses every such target to just **two possible predecessors**, each with odd second counter at least five and coordinate sum two modulo four, contradicting the source-proved `Agent3.blank_section_odd_image`. The proof holds for all unbounded natural counters and blank-section times. There is no simulation horizon, no finite state-quotient assumption, and no invented transition model. [C23Rectangle.lean](C23Rectangle.lean) contains the complete proof.

The [C23High.lean](C23High.lean) theorem `blank_no_high_sum23_right4` pulls this invariant back through the original HIGH stopping equation. Every high pair satisfying

```
2≤m, j%4=0, (j+7)%32=(3*m)%32
```

has an unreachable stopping target. This comprises **eight of the 1024** `(j,m)` congruence pairs modulo 32, a strict new **1/128** high-sector barrier (for parameters with `m≥2`). These pairs are disjoint from both high 1/70 modulo128 exclusions below. [C23Integration.lean](C23Integration.lean) proves the newest exact two-sided blank-halting equivalence with this restriction conjoined to all older gates.

Most importantly, [C23Strict.lean](C23Strict.lean) proves

```lean
previous_high_admits_sum23 (j m : Nat)
    (hm : 2≤m) (hj : j%4=0)
    (hpair : (j+7)%32=(3*m)%32) :
    BB6.Agent24Phase.highAllowed j m
```

for **every** pair in this family. The proof reconstructs the entire previously integrated source high predicate, including both independent unbounded dyadic exclusions, four odd-source branches, all modular and valuation-six gates, and the genuine affine right-four normalizer. Thus these are not rediscovered prior exclusions. The local Lean check of all four C23 files succeeded with source-identical definitions and exact theorem interfaces; complete unchanged upstream-source CI remains pending. Until it succeeds, treat the results as promising intermediate mathematical work.

---

## Additional three-layer 1/70 rectangle

Let `CReach a k` be exact finite-time reachability of the original Machine C section map `BB6.Agent46.secNext` starting at `(5,1)`. The primary proposed theorem is

```lean
BB6.Agent20C70.blank_no_rect_1_70_mod128 (s t : Nat) :
  ¬ BB6.Agent3.CReach (128*s+1) (128*t+70)
```

**This is a genuine two-dimensional excluded cylinder**: both parameters are unrestricted, and there is no finite simulation horizon. It subsumes the single-right-counter ray `¬CReach 1 (128t+70)`. It would be a new nontrivial result even if no Machine C stopping family existed.

### Exact source fibre

For `secNext(a,k)=some(x,y)`, provided `6≤y`, `y%2=0`, and `(x+y)%16=7`, the `seven_inverse_iff` theorem in [SevenInverse.lean](SevenInverse.lean) establishes the full equivalence with precisely these two source branches:

```
DIRECT: a=x+y-2, y=2*k+2

ODD BOUNCE: 3≤a, a%2=1, a<2*k,
            x+y=4*a+11, x+2*y=2*k+a+10
```

The proof is exhaustive over the source machine's `sectionPreimageAll` definition, including `a=0,1`, direct, and both recursive bounce branches. The crucial valuation fact is that `(x+y+1)%16=8` forces odd-bounce depth exactly one. A depth of two or more forces divisibility by 16; depth zero contradicts the parity of the exact bounce cost.

### Exhaustive reverse tree

With root `R=(128s+1,128t+70)`, all actual predecessors lie in this finite tree:

```text
R
├── O=(32s+32t+15, 48s+112t+58)
│   └── (80s+144t+71, 24s+56t+28)
│       └── L1=(104s+200t+97, 12s+28t+13)
└── D=(128s+128t+69, 64t+34)
    ├── (32s+48t+23, 48s+104t+52)
    │   └── L2=(80s+152t+73, 24s+52t+25)
    └── (128s+192t+101, 32t+16)
        └── L3=(128s+224t+115, 16t+7)
```

The source-proved six-residue even-right inverse theorem forces all single-child links; exact `seven_inverse` determines the two split nodes. The three leaves have odd right coordinate at least seven and coordinate sum congruent to two modulo four. The exact source theorem `BB6.Agent3.blank_section_odd_image` forbids all such states after the blank seed; none of them is `(5,1)`. Therefore the root is unreachable for all natural `s,t`.

## Consequences for the original machine's stopping criterion

The original low stop equation is `k+3m+4=2^(2m+3)`. Its parameter class `m%128=18` forces `k%128=70`, so `blank_no_low_depth_18_mod128` rules out the entire class. [C70Integration.lean](C70Integration.lean) proves the previous canonical predicate `BB6.Agent11C58ValSix.lowAllowed (128t+18)` holds for **every** `t`; therefore this low exclusion is *strictly stronger* than that earlier integrated sieve, assuming the source compilation passes.

The high stop equation is `k+j+3m+5=2^(2m+2)*(j+3)` and source left counter `a=2j+3`. [C70Rectangle.lean](C70Rectangle.lean) proves that the new 1/70 rectangle excludes both complete high parameter cylinders

```
(j%128,m%128)=(63,82)
(j%128,m%128)=(127,18).
```

The [C70Integration.lean](C70Integration.lean) theorem `blank_halts_iff_c70_both` gives an exact, two-sided halting characterization with all **three** new exclusions conjoined to the previously strongest joint C58/ValSix plus exceptional-phase criterion. The low-family restriction is independently provably new relative to that previous predicate. **[C70Strict.lean](C70Strict.lean)** proves the stronger uniform theorem `previous_high_admits_rectangle`: both full high index cylinders satisfy the *entire* previous integrated `BB6.Agent24Phase.highAllowed` sieve, including the older unbounded dyadic quantifiers, odd-depth restrictions, and the source affine normalization guard. Thus the high exclusions are also strictly new relative to this full previous integrated predicate. This strictness proof was checked locally in Lean 4.36.0-rc2 against source-exact reproduced definitions, with no new axioms; original-source CI is still outstanding.

## Reproducibility

The full work is divided into [SevenInverse.lean](SevenInverse.lean), [C70Root.lean](C70Root.lean), [C70Rectangle.lean](C70Rectangle.lean), , [C70Integration.lean](C70Integration.lean), and [C70Strict.lean](C70Strict.lean). The manual workflow pins and compiles the original upstream `GenericSection`, `FastSectionDef`, `SectionAllInverse`, `Agent3COrbitIff`, `EvenRightSixOrbit`, `StrongJointResidual`, and the Agent11/27 proof chain before compiling these modules. Every final theorem prints its dependency axioms.

The local proof-body test used *exactly typed source-interface stand-ins*, with audit outputs containing the stand-in names; consequently local acceptance alone is **not** original-source validation. Those stand-ins are deliberately absent from the committed research proof files.

## Boundaries

No claim is made that Machine C fails to halt, that BB(6) has been determined, or that any currently unknown global halting/nonhalting decision is resolved. Each family is only a necessary gate restriction on the existing unbounded stopping criterion.
