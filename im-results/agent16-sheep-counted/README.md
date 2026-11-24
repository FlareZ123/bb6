# Exact primitive-transition accounting for Sheep

The literal six-state machine 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE is formalized with finite tape lists and implicit infinite blanks. The indexed Trace relation checks each transition, including all sweeps and the initial blank prefix. Score counts successful moves plus the final undefined transition query.

## Exact theorem

```lean
theorem blank_score_iff (s : Nat) :
    Score s blank ↔ ∃ a c, WPath c 5 (2^a*4) ∧ s=12+c+powerLive a
```

The raw machine enters section 5 in 11 live moves. For P(m,k) = 0^∞1^m E> 1 1^k 0^∞, the exact live costs are:

| Source | Live cost |
|---|---|
| P(0,0) | 7 |
| P(0,k+1) | 5 |
| P(1,k) | 8 (then one halt query) |
| P(2m+2,k) | (4m+7)k+6m²+21m+14 |
| P(2m+3,k) | 2m²+11m+16 |

For t=2^a u, u odd ≥5, the next section is t+a+(u-1)/2 with cost C satisfying
6C = 4t²+12tu-24t+12(u-1)a-7u²+9u-24.
For u=3, next is t+a+3, and 3C+15=2t²+18t+24a.
For terminal t=2^j, j≥2, the live cost plus halt query satisfies
3C+3t=2t²+3j+1.

The exact score iff is proved by strong induction on the real live halt count, using deterministic stripping of indexed macro traces, not just forward simulation. No terminal path from 5 is established.

## Reproduction

Run python reconstruct.py; then lean SheepCounted.lean using Lean 4.36.0-rc2, import Std only. Local compiler succeeded; final blank_score_iff depends on propext and Quot.sound. No sorry or native_decide. The independent literal-table semantics is now proved equivalent to two infinite tape streams in SheepStream.lean, including both directions of the exact score statement; it is not imported into the upstream BusyBeaver library. SheepCountedBridge.lean proves both directions of the unweighted path equivalence with the existing SheepEven.Steps model. Upstream uncounted source: google-deepmind/cryptids revision ced8f9f44f67a167d5ecc03e687b048c67926371, Sheep machine module.

Intermediate result: exact score reduction, no new attained lower bound or whole-machine decision.

## Primitive-cost potential and halting exponent

Define P(x)=6(x-1)^2+5(x-1). Every odd-source section return x>=5 of cost C satisfies the exact identity

    5C+25+P(x)=P(y).

Every section edge has C<=2x^2 for x>=5. If M is the sum of x^2 over even-source returns only, every weighted path from 5 to T satisfies 5C+P(5)<=10M+P(T). Odd costs therefore telescope without a count factor. With T=2^j, the exact score S obeys the kernel-checked inequalities

    2T^2+33 <= 3S+3T,
    15S <= 165+30M+28T^2.

Paper composition with ../agent16-sheep-band-residence/: for k,r>=1 and j<=r(k+1), put B=(j+1-k)^r+(2^k+1)r+1. Each dyadic band below T contains at most B even-source returns (internal edges plus the last crossing). Therefore M <= (4/3)B(T^2-1) and

    15S <= 165+40B(T^2-1)+28T^2.

In particular log2 S=2j+O(sqrt(j log(j+1))) for any halting orbit, by the earlier choice of k,r. This is a conditional score estimate, not a bound on j. The last composition is a written mathematical argument; the cost and potential theorems themselves are kernel-checked.

Extensions: python reconstruct.py extracts the three additional Lean files. Compile SheepCounted.lean and the unchanged SheepEven.lean to .olean in one directory, then check SheepStream.lean, SheepPotential.lean and SheepCountedBridge.lean with LEAN_PATH=. . All three compiled locally; final axiom reports are subsets of propext, Classical.choice, Quot.sound.
