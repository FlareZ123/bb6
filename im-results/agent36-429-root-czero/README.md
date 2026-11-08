# Authentic blank-origin #429 C/0 right-record stress test (8 Nov 2026)

**Status: finite computational reconnaissance in the exact 12-entry original machine table; not an unbounded mathematical proof.** This is targeted directly at the open root-sensitive hypothesis of [Agent32's original-source theorem](../agent32-429-raw-parent/BB429FreshFrontier.lean) and the [8 November Critic directive](../../communications/broadcast/20261108T2134Z_Critic-429-C0-root-closure-over-synthetic-families.md).

`blank_czero_record.cpp` is a standalone dependency-free C++17 original-machine simulator for `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, initially blank tape, state A, head 0. It maintains the **strictly earlier** maximal head position before every C/0 test, tests whether the immediately-right tape bit is 1, then performs one genuine primitive transition. The fixed tape buffer covers positions ±12 million and detects out-of-range access; actual observed visited range is far smaller. Compile with `g++ -std=c++17 -O3 -Wall -Wextra -Werror blank_czero_record.cpp`, run binary.

Reproduced output (100 million executed defined transitions; no observed halt):

```text
STEPS=100000000 C0=222 NONRECORD=0 C01=0 MAX_VISITED=753 MIN_VISITED=-2596
```

All **222** C/0 instruction-start events were at strictly new rightward head records. In fact the full event sequence recorded by an exploratory logging variant had `head=previousHeadMaximum+1` at all these events. Each had a blank right neighbor. The first C/0 records were at steps/heads `(2,2),(13,5),(64,8),(111,11),(275,15),(366,18),(882,22)`; their record-head increments were always 3 or 4 in this prefix.

This does **not** imply that every future C/0 is a head record or that machine #429 never halts. The user-facing theorem needed is an original-source Lean proof quantified over **every genuine blank-root instruction time**, showing the C/0 frontier property or the weaker C/01 absence. The finite experiment favors pursuing the established head-record candidate over assuming it false. Existing source-certified conditional Junc return C/0 census [Agent1](../agent1-429-w4-boundary/README.md) must be connected to an exhaustive genuine blank-root return grammar before it can settle the question. Another local-factor invariant attempt has already failed [Agent6](../agent6-429-regular-screen/README.md); simple widening of finite factors is unlikely to be decisive.
