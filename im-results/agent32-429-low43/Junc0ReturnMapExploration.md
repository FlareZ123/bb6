# Junc(0,w) return-map exploration

**Status:** exploratory deterministic simulation plus algebraic composition plan. This is not a Lean theorem and does not prove an infinite run.

## Observed return sequence

Starting from the prepared Junc state J(0,344), the original six-state transition table was simulated for 20,000,000 steps. The following Junc(0,w) checkpoints were observed (times are relative to the J(0,344) input):

| Step | w |
|---:|---:|
| 0 | 344 |
| 145,374 | 408 |
| 196,453 | 436 |
| 251,186 | 464 |
| 311,141 | 492 |
| 377,886 | 520 |
| 452,989 | 548 |
| 538,018 | 576 |
| 634,541 | 604 |
| 744,126 | 632 |
| 868,341 | 660 |
| 1,008,754 | 688 |
| 1,166,933 | 716 |
| 1,344,446 | 744 |
| 2,502,495 | 924 |
| 3,193,805 | 1,008 |
| 3,738,578 | 1,060 |
| 4,412,233 | 1,112 |
| 8,369,585 | 1,356 |
| 16,958,173 | 1,668 |
| 19,595,676 | 1,756 |

The simulation was continued to 20M steps without reaching a halt. Treat these as experimental observations only.

## Exact algebraic candidate for the repeated +28 branch

For w divisible by 4 with 408 ≤ w ≤ 736, define j=(w-360)/2 and k=(188-j)/2. Then j is even, k is a nonnegative integer, and j+2k+1=189, 2j=w-360.

The existing outer-safe macro formulas give:

1. Five outer-safe steps U=0,3,9,21,45, taking J(0,w) to J(93,w-171) in 11,139 steps.
2. One outer-safe step U=93, taking J(93,w-171) to J(189,w-360) in 35,553 steps.

The generic low42 endpoint formula for input J(j+2k+1,2j) then applies to J(189,w-360), and returns J(0,4j+4k+12)=J(0,w+28). Its source/physical step count is 4j²+22j+18k+79. Thus the full candidate return time is

T(w)=46,692+4j²+22j+18k+79
    =(w-360)²+13((w-360)/2)+48,463.

This predicts the observed sequence 408,436,464,492,520,548,576,604,632,660,688,716,744. At w=744, the formula gives j=192 and k=-2, so this low42 branch no longer applies; the observed next return is J(0,924), indicating a different regime.

## Formalization opportunity

The endpoint/time map should be formalizable by composing:
- the existing outer-safe Junc macro;
- the second U=93 outer-safe step;
- the generic low42_raw_head_all theorem in im-results/agent6-429-low42/Low42Physical.lean.

The main technical step is lifting the generic low42 physical result to the represented Junc input and composing it with the outer-safe physical segments. The nofatal prefix property is not yet generalized here. A successful physical run to a nonhalting Junc endpoint already proves finite nonhalting for that segment; a generic C/01-prefix lemma would additionally preserve the repository's stronger guard invariant.

The special transition J(0,344) -> J(0,408) is included in the current draft PR #83 blank-root chain, but this repeated +28 family is not yet part of its Lean declarations. Do not cite the simulation table as proof or infer infinite nonhalting from it.


## Candidate generalization of the nofatal guard

A useful lemma for the parameterized return map is likely:

If the ordinary source run satisfies `run n z = some z'`, and the endpoint is neither the halting state D/1 nor a `fatalCZero` state, then `runNoFatal n z = some z'`.

Reason: any `fatalCZero` state is C/0 with a marked immediate right neighbor. Its next transition enters D/1. If that state occurs before the final prefix, the ordinary run cannot continue past D/1; if it occurs exactly one step before the endpoint, the endpoint would be D/1; if it occurs at the endpoint, the endpoint is fatal. All three cases contradict the hypotheses. An induction on n should turn this into a small source-level lemma in `NoFatalGuard.lean`.

This would let researchers derive `runNoFatal` from existing generic successful source-run theorems with safe Junc endpoints, rather than proving each low42 parameter instance by `decide`. It is a proof sketch only and has not been formalized or kernel-checked.

Substituting w=408,436,...,716 into T(w) gives interval times 51,079; 54,733; 59,955; 66,745; 75,103; 85,029; 96,523; 109,585; 124,215; 140,413; 158,179; and 177,513. Their sum is 1,199,072, exactly matching the simulated interval from J(0,408) to J(0,744). Combined with the observed 145,374-step J(0,344)->J(0,408) segment, the simulation reaches J(0,744) 1,344,446 steps after J(0,344), or step 1,514,038 relative to the candidate blank-root prefix at step 169,592. This remains a conditional extrapolation until the generic physical composition is formalized.

A useful route for the physical lifting gap: `low42_raw_head_all` starts from a canonical physical config with head 0, whereas a `Represents` witness for Junc may use any absolute head coordinate. Define a tape/head translation `translate d c` by moving the head to `c.head+d` and setting the new tape at x to `c.tape (x-d)`. Prove `rawStep` commutes with this translation, then induct on n to show `run` commutes with translation. This transports the canonical low42 physical theorem to any physical config represented by the matching Junc zipper. The endpoint representation and outer-safe physical segments can then be composed without per-(j,k) `by decide` proofs.
