# BB429 guarded affine pump and 39,049-step rooted trace compression

**Agent 6, 2026-11-05. Intermediate formal mathematical result.** #429 and BB(6) remain undecided. The two Lean source files [Agent6Pump.lean](Agent6Pump.lean) and [Agent6Pump15.lean](Agent6Pump15.lean) have compiled under Lean 4.36.0-rc2 against exact earlier source-verified theorem signatures; **full unchanged-repository-source compilation still awaits a manual CI run**. The observed blank-origin entry to this pump has been independently checked by a local exact twelve-branch simulator but is **not yet part of the Lean theorem**.

## General symbolic source-map pump

Let `BB429.next` be the unchanged original repository 12-branch accelerated map; `BB429Burst.firstRun` denotes a first-branch-only prefix. Suppose the first-only prefix starting from `(11,w)` runs for `L` transitions, ending at `(u,b)`, and
```text
b >= 3, b odd,
d := u-floor(b/2) >=4, d even,
b <= d+7.
```
Then the next two genuine **non-first** source transitions are
```text
(u,b) -> (d+7, 2*b-4) -> (11, w+3*L+31).
```
Here the first arrow uses the **odd-second-counter / even-gap** case and the second the **even-second-counter / even-gap** case. The rank invariant for the prefix, `2u+b=22+w+3L`, yields the return value algebraically. Hence:
```text
BB429.run (L+2) (11,w) = some (11,w+3*L+31).
```
This is the exact universally quantified theorem `Agent6Pump.pump`. It exhibits a linear-return mechanism for long sections of the map with no zero-first-counter reset; it applies to arbitrary valid `L,w,u,b`, without any finite rollout. The guards are essential, especially the **non-saturating inequality b<=d+7**; using `d-b+9>=2` with natural subtraction would incorrectly permit a saturated value. The Lean proof checks the genuine branch conditions.

## Specialization: a continuous 39,049-step pumping section

Set `L=15` and, for `0<=j<=2296`,
```text
w_j = 1048722+76*j
u = 14*2^15-3 = 458749
b_j = 131291+76*j
d_j = 393104-38*j.
```
`BB429Burst.prefix_exists_iff` and its exact `prefix_formula` show the 15-step first-prefix from `(11,w_j)` ends at `(u,b_j)`. The decisive guard is
```text
b_j <= d_j+7  iff  114*j <= 261820,
```
true for every `0<=j<=2296`. The other even/odd and lower-bound guards hold uniformly in this range. Therefore:
```text
BB429.run 17 (11,1048722+76*j)
  = some (11,1048722+76*(j+1)),  for every j<=2296.
```
The induction theorem `Agent6Pump15.run_cycles_2297` gives the **entire** section
```text
BB429.run 39049 (11,1048722) = some (11,1223294).
```
This uses one symbolic induction over 2,297 periods, avoiding evaluation of 39,049 individual transitions in a formal proof. At `j=2297`, the second-branch guard fails: `b=305863 > d+7=305825`, so the cycle legitimately exits. The pump does not prove infinite nonhalting.

## Connection to the genuine blank run (computational evidence)

A separate exact Python simulator of the same 12-branch transition definition, seeded at genuine blank `(0,0)`, found the following **macro** indices and exact states (no machine-step counts are implied):

| Macro index | (u,w) | Current macro branch |
| ---: | :--- | :--- |
| 275305 | (0,1048576) | first |
| 275342 | (393149,262426) | even-w even-gap |
| 275343 | (11,1048722) | first, the pump entry |
| 314391 | (305863,611570) | even-w even-gap |
| 314392 | (11,1223294) | first, the pump exit |
| 314410 | (611622,138) | even-w odd-gap |
| 314411 | (0,1223392) | first |

The difference `314392-275343=39049=2297*17` matches the symbolic Lean theorem. **Crucial provenance distinction:** the 39,049-step section from the stated entry is locally Lean formalized; the assertion that blank reaches the entry at macro index 275343 is so far a separate exact computational trace, not a proof in Lean. The accelerated map itself has previously been bridged elsewhere in the project to the pinned original six-state machine, but this experiment is conducted on the in-repository source map. Do not infer any resolved BB(6) bound.

## Interpretation

The observed 39,106-step gap between two zero-first-counter visits is mostly accounted for by this 39,049-step guarded affine pump. Such large false-plateau phases complicate arguments that every short window contains a zero-first reset. The general pump lemma gives an exact guard for stopping the apparent 17-step cycle. This is potentially reusable in a root-sensitive phase decomposition and for accelerated symbolic reachability, although no globally valid blank invariant or genuine halt decision has yet followed.

A valuable follow-up is to formalize the **root-to-entry** finite macro certificate via a verified accelerated evaluator or a chain of compact symbolic burst certificates, and to find a **structural invariant governing all pump entries** rather than lengthening a finite rollout. This dossier belongs in `im-results/` until it yields a genuinely open-problem-relevant new mathematical theorem.
