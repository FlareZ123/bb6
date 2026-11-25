# Canonical raw107: five-hole B1=0RD child candidate and six-hole census

Parent: `1RB---_1RC---_0RD---_1LD1RE_---0RB_------`. This is canonical residual 107, with six holes. The first undefined row is B1 at time 7. This work closes a candidate **two-child** audit, not the whole parent or the BB(6) upper bound.

## B1=0RD child

The child is `1RB---_1RC0RD_0RD---_1LD1RE_---0RB_------`. Its first query is E0 at time 15. Candidate weighted bound: **129**. The finite enumeration accounts for all 9,765,625 raw assignments (25^5): cycle mass 9,172,475; halt mass 559,887; total-defined nonhalt mass 32,088; previously open mass 1,175. The tree has 406 split, 7,955 cycle, 1,337 last-hole and 47 formerly open nodes. The largest finite score is 129 (ordinary time 126, delay 2): `1RB0RE_1RC0RD_0RDHHH_1LD1RE_0LF0RB_0LA1LE`.

All 47 previously open nodes now have candidate certificates: 40 one-state forward FAR witnesses, two three-state forward FAR witnesses, and five exact symbolic sweeps. The five entry and universally quantified growth theorems were compiled locally with Lean 4.36.0-rc2 using copied exact zipper/sweep primitives and proved lemmas. The original-source import closure, FAR checks, tree checks, and weighted certificate remain **pending**; no accepted roster reduction claimed.

| Leaf | Entry time | Cost for n→n+1 |
|---|---:|---:|
| 0 | 2 | 50+20n |
| 2 | 81 | 49+14n |
| 3 | 1097 | 481+76n |
| 30 | 15 | 51+48n |
| 36 | 16 | 19+8n |

Leaf 3 is the long-epoch case: filter fresh-boundary observations to t≥1097, choose left boundary and state E (4), period 1. A length-eight periodic tape block is transferred through multiple sweep phases. The resulting unbounded recurrence is stronger than the finite discovery trace. Local entry axiom sets were [propext]; growth [propext, Quot.sound], no sorryAx/native_decide.

Run `python generate.py` to regenerate the candidate Lean modules using the existing repository tools. Open roster SHA256: 498535eee6ac4a86e2deaf8b0297db04339047757a1e3f99a31b7e5700bab61c. Compile Raw107RDData.lean and inspect its axiom profile with the established original-source workflow. Direct local git checkout failed DNS and the available connector exposes no workflow dispatch method; local copied primitive checks are not original-source CI.

## B1=0RC child

The child `1RB---_1RC0RC_0RD---_1LD1RE_---0RB_------` first queries C1 at time 16. Candidate weighted bound **200**. Counts: 1007 split, 19427 cycle, 3343 last-hole, 392 formerly open. Mass: 8,022,875 cycle; 694,518 halt; 80,232 total ordinary-only nonhalt; 968,000 open; total 9,765,625. Max finite score 200 at `1RB0LA_1RC0RC_0RD1LF_1LD1RE_1RA0RB_1LEHHH` (199 ordinary steps, zero delay).

All 392 open leaves have candidates: 390 FAR masks and two symbolic sweeps. Leaf 102 has entry 2 and cost 17+20n. Leaf 100 (E0 hole) is the exponential countdown `1RB0RF_1RC0RC_0RD0RA_1LD1RE_---0RB_0RC0LD`; its family is state D with zipper left 0^(3n+4)11 and empty right. Raw107RCCountdown.lean proves the binary decrement and clearing recursion with arbitrary uninspected suffix. C(0)=0, C(n+1)=2C(n)+10+6n; epoch cost C(n)+6n+11; entry 9. Entry and growth compiled locally against copied exact zipper/sweep primitives (propext, Quot.sound). The original-source never theorem and complete audit remain pending. Generate using `python generate_rc.py`, compile Raw107RCData.lean. Open roster SHA256: 9d6ea5784163259089bd5f03f627ffc8ecd8d5bfe361a07c7be7bdeefcd25551.

## Full raw107 census

Finite enumeration accounts for all 244,140,625 assignments: cycle mass 221,509,400; halt mass 18,357,404; total-defined nonhalt mass 1,291,296; open mass 2,982,525. Tree counts: cycle 231224, last 53804, split 12816, open 9741. Max finite weighted score 815, not a global bound. Existing FAR candidate bank screening found 9411 hit leaves and 330 unresolved before the five child sweeps. These remain exploratory saturation outcomes, not formally certified coverage. The 0RD subtree is the first fully witnessed nontrivial child investigated here. Other child closures and source integration remain the next tasks.

