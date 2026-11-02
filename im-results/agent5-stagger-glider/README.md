# Agent 5: four-step staggered glider cylinders

**Classification:** intermediate whole-machine nonhalting certificates. No BB(6) upper bound or undecided holdout status is established here.

## Certified mathematical statement

With state A as blank start and a bi-infinite blank tape, fix arbitrary symbols `a,u,v,w ∈ {0,1}` and states B,C,D. Four ordinary, assigned transitions are:

```
A/0 → write a, R, B
B/0 → write v, L, C
C/a → write u, R, D
D/v → write w, R, A
```

Starting in A at position x with the tape blank from x rightward, these four moves follow head positions `x→x+1→x→x+1→x+2`. The head returns to A and again faces a pristine right half-tape. The invariant iterates indefinitely. The same proof reflected left/right holds for leftward gliders, and the remaining eight slots may be completed arbitrarily.

`ShiftBounce.lean` proves `stagger_never` for any complete machine, `partial_stagger_cover` and `partial_left_stagger_cover` as actual `Cover (DecidedBelow bound) p` certificates for all compatible completions, and an explicit `example_stagger_cover`. The proof imports the unmodified original Agent8 `Frontier.lean` and `Symmetry.lean`. It prints the final Lean kernel axioms.

Decoded file: `ShiftBounce.lean.xz.b64`, SHA-256 **a4e380c1db02652dc4cb272d03bc01109c06149b6926dfa348bf6bb97793ff4a**. Locally Lean 4.36.0-rc2 compiled with matching upstream interface declarations and no `sorry`; an original-source CI audit is the stronger necessary validation.

## Exact symbolic census

To produce disjoint *four-distinct-slot* cylinders, require B≠A and C≠A, and discard any parameter choice repeating an assigned (state,read-bit) source slot. The C≠A restriction avoids a previously documented four-step family with B/0 returning immediately to A. With two mirrored directions, each has 900 cylinders with a=1 and 720 with a=0, for **3,240** cylinders total.

Every four-slot cylinder fixes four nonhalting transitions, leaving eight arbitrary slots. The combined exact full-table mass is **494,384,765,625,000 = 3,240·25^8**, or **0.82944%** of the `25^12` full table universe. Among full tables with exactly one halt, the new family covers **118,881,339,310,080 = 3,240·8·24^7** tables, **0.65104167%** of `12·24^11`.

The deterministic `census.py` independently enumerates this family and the earlier Agent6 set: 120 three-step, 380 four-step, and 120 turnaround cylinders. It checks **7,447,870** distinct pairs for incompatible transition requirements. **All 3,860 cylinders are pairwise disjoint.** Their union covers **1,541,137,695,312,500 = 2.5856%·25^12** full tables. This union statement includes only Agent6's enumerated three sets, without making a completeness claim about other existing nonhalting proof families.

Decoded file: `census.py.xz.b64`, SHA-256 **21eafab86ed664d392d5f2e95f58fa53207974300fcf0a993c5fb60c99985c3d**. The census is an explicitly reproducible finite calculation, not a Lean kernel theorem about cardinalities. The infinite-run and sparse-cover Lean theorems do not depend on this counting code.

## Reproduction and limitations

The manual workflow `.github/workflows/agent5-stagger-glider.yml` recompiles the **unmodified** original Agent8 semantics and symmetry, decompresses both archived sources, checks SHA-256, compiles the new Lean module and audits its axioms, then runs the entire census. Nothing runs per commit.

These are easy-machine nonhalting cylinders potentially useful to a sparse proof-carrying search. They do not decide any historic unresolved root, complete a global six-state coverage tree, establish a Busy Beaver upper bound, or establish the exact BB(6) value.
