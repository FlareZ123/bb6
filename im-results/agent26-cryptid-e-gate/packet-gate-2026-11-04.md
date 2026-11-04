# Agent 26 (2026-11-04): source-audited A/E exceptional packet returns

**Status:** All-parameter intermediate theorems for the literal D-start six-state two-symbol machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Original blank-tape halting remains unresolved; no new BB(6) bound or independent external novelty is asserted. Retain in `im-results/` pending evaluation.

Let `I_n(s)` be state F scanning 0, physically blank to the left, right infinite tape `1^n s 0^∞`. An A boundary of length m is A/0 with nearest-first left `0(10)^m11`; an E boundary is E/0 with left `00(10)^m11`.

## New universal identities, fully kernel checked against original source

1. **A suffix 1101010111**: [A1101010111.lean](./A1101010111.lean), [A1101010111First.lean](./A1101010111First.lean). For all m≥0 and arbitrary finite Y, `A_m(1101010111Y) --[2m+36]--> I_(2m+5)((01)^4 0Y)`, and the return is the **first physically blank-left F/0**. Consequently `I_(3k+3)(0 1101010111Y) --[12k²+49k+74]--> I_(8k+11)((01)^4 0Y)`.

2. **E all-q suffix (10)^q1101010111**: [E1101010111Pairs.lean](./E1101010111Pairs.lean), for all k,q≥0 and arbitrary Y:
```
I_(3k+4)(0 (10)^q 1101010111Y)
  --[12k²+49k+80+4q]-->
I_(8k+5)(0 1^(2q+6) (01)^4 0Y).
```
The proof uses source scanner, 33-step A turn, reverse C sweep and existing B sweep, with exact original primitive-step times. The strict first *physically blank-left F/0* return is also proved in [E1101010111First.lean](./E1101010111First.lean), using a source-preserving scanner, C-walk, C/B handoff and B-sweep no-return decomposition. An earlier state-F visit with nonblank left tape is correctly excluded from the return criterion.

3. **Arbitrary A token-code prefix**: [A1101010111Code.lean](./A1101010111Code.lean) composes universal `CryptidA.wordCode` consuming tokens 10 and 111 in any order with the new A terminal. For all k, finite token sequences w and arbitrary Y, `I_(3k+3)(0 wordCode(w) 1101010111Y)` returns exactly after `12k²+41k+32 + wordCost(4k+3,w) + 2m+36`, where `m=4k+3+wordInc(w)`, to `I_(2m+5)((01)^4 0Y)`. The combined token-code source also has a **stronger strict first physically blank-left F/0 return** in [A1101010111CodePhysicalFirst.lean](./A1101010111CodePhysicalFirst.lean). Unlike the preceding [A1101010111CodeFirst.lean](./A1101010111CodeFirst.lean), which excludes only syntactically empty-list intermediate F/0 sections, the strong theorem excludes every F/0 configuration whose entire physical left tape is blank, even if its zipper list contains explicit false cells. Both compile against the unchanged source.

4. **Two shorter A terminals**: [A110101Closure.lean](./A110101Closure.lean) proves for every m,Y:
```
A_m(11010111Y)          --[2m+30]--> I_(2m+5)((01)^3 0Y)
A_(m+1)(110101010100Y) --[2m+34]--> I_(2m+3)(0 1^14Y).
```
**Critical correction:** An initial unguarded statement `A_(m+1)(1101010101Y)` at the second duration is **false** for arbitrary Y. Independent simulator, e.g. m=1,Y=11, first returns at 44 rather than 34. Original-source Lean correctly rejected the unguarded statement; the extra explicit `00` was added and reverified in CI. Do not remove that necessary guard.

## Strict source status and connection to the outstanding packet problem

Original source Lean 4.36.0-rc2 CI [41866562409](https://github.com/FlareZ123/bb6/actions/runs/41866562409) **SUCCEEDED** for A 1101010111 exact/strict and E all-q endpoint. Stronger run [41868760696](https://github.com/FlareZ123/bb6/actions/runs/41868760696) **SUCCEEDED** for corrected shorter A terminals and arbitrary mixed-code A terminal, with `#print axioms` exactly `[propext, Quot.sound]` and no `sorryAx` for final new theorems.

Independent literal-table [check_new_returns.py](./check_new_returns.py) tests 2,311 parameterized synthetic configurations at exact first physical return times and whole physical tape, with fixed seed 20261104; this is supporting finite evidence.

Agent31's abstract packet notation `M(a,q,p;Y)=I_a((01)^q 0 1^p Y)` with fixed tail `Y=01010111` enters the new E branch in the p=2 exceptional case. The source-proved reset, with **the marker changing**, is
`M(3k+4,q,2;01010111 Z) → M(8k+5,0,2q+6;010101010 Z)`.
The extra final zero in `010101010` is a *physical tape cell* whenever arbitrary suffix `Z` is nonempty; for `Z=[]` only, it can be erased as an implicit right blank. Critically, an earlier draft claimed the output retains the original suffix `01010111`; **that claim was false** and is explicitly withdrawn. The correct source theorem outputs `0 1^(2q+6) (01)^4 0 Z`. Since the tail marker changes and the new `p` may increase, a single fixed-tail rank argument is insufficient. This result does not establish a global closure, blank-orbit reachability or a halt decision.

Future research: identify a global packet invariant or amortized rank surviving the reset, and connect long synthetic chains to authentic blank-origin reachability.

**Stronger CI:** [manual run 41870397910](https://github.com/FlareZ123/bb6/actions/runs/41870397910) also SUCCEEDED for the complete E strict-first-return theorem. The audited dependencies of `e_front_firstPhysical`, `e_firstPhysical`, and `full_E_1101010111_first_return` are precisely `[propext, Quot.sound]`, without `sorryAx`.

**All-code strict CI:** [manual run 41871559177](https://github.com/FlareZ123/bb6/actions/runs/41871559177) **SUCCEEDED** against the unmodified original table, including all `ACodeFirstReturn` / `AExceptionalClosure` imports and `#print axioms full_A_code_1101010111_first_return` = `[propext, Quot.sound]`. The same run independently executed all **2,311** literal-table first-physical-return regression cases with zero discrepancies.

## 2026-11-04 follow-up: source-certified E-to-B two-return reentry for k divisible by 3

Source [E1101010111ThenB.lean](./E1101010111ThenB.lean), [manual original-source CI 41872994675](https://github.com/FlareZ123/bb6/actions/runs/41872994675) **SUCCEEDED**, with `#print axioms e_then_b_simplified` exactly `[propext, Quot.sound]`. For all t,q≥0 and all arbitrary physical right suffix Z, it composes the E exceptional first return at k=3t with its subsequent B-delimiter return:

```
I_(9t+4)(0(10)^q 1101010111 Z)
   --[876t² + 731t + 181 + 4q original primitive transitions]-->
I_(64t+2q+23)((01)^4 0 Z).
```

The unnormalized original-source theorem literally returns `1^(64t+17) 1^(2q+6) 010101010 Z` at F/0 with physically blank left; the new count `64t+2q+23` only combines adjacent ones. **For Z empty**, the terminal zero is an implicit blank, so this output lies in the formerly known regular language `L(a,4,0)=I_a((01)^4)`. For arbitrary nonempty Z, the extra zero remains real and the output has the displayed changed right suffix. Consequently, this settles a *subfamily* of the synthetic E p=2 exceptional resets at `k≡0 (mod3)` with empty continuation, without asserting that these inputs occur on the actual blank-machine orbit.

Independent literal machine [check_e_then_b.py](./check_e_then_b.py) covered **1,056** actual first-physical E-then-B pairs, with full tapes and both elapsed step counts, in the same successful CI run. This finite test is supplementary to the all-natural Lean endpoint proof. Cases k≡1,2 (mod3) and actual blank-root reachability remain open.

**Strict physically blank-left code audit:** [manual source CI 41873417571](https://github.com/FlareZ123/bb6/actions/runs/41873417571) also compiled `full_A_code_1101010111_firstPhysical` and printed only `[propext, Quot.sound]`. This is the authoritative whole-code first-physical-return theorem; use this stronger statement when composing machine F-sections.
