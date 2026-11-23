# Cryptids #429: rooted 29-mod-32 odd-reset inverse restriction

**Status:** Lean source proposed; pending compiler diagnostic and complete transitive axiom audit. This is an intermediate restriction, **not** an exact #429 or BB(6) decision.

The actual-blank local accelerator is `BB429.run`, with source transition `BB429.next` in `im-results/agent5-429-rank/BB429Rank.lean`. The exact odd-reset source family `(u,w)=(32q+29,64q+55)` was one of three surviving residue cylinders in the earlier source-connected `BB429Branch7Source.lean`.

New inverse calculation in `BB429Branch29.lean`: for `q>=21`, if the authentic blank-root macro orbit reaches `(32q+29,64q+55)`, necessarily `q mod 8 = 2 or 7`. It is an all-time parameter exclusion for six residue classes, not an exhaustive branch-7 closure. The five forced predecessors, starting from the output, are

```
(32q+29, 64q+55)
(16q+13, 96q+84)
( 8q+ 5,112q+97)
( 4q+ 1,120q+102)
( 2q- 1,124q+103)
(   q- 2,126q+102)
```

At the fourth state, the alternative odd inverse would have parent `(34q+20,60q+53)`, impossible for an actually reached positive even first counter (its second counter is odd). For odd q, the last state has forced predecessor `(x,127q+100)` with `2x+5=q`.

The contradiction cases use *existing rooted* modular theorems, not heuristics: q divisible by 4 violates `rooted_one_strong` at `(4q+1,120q+102)`; q=1 mod8 violates `rooted_five_strong` there; q=6 mod8 violates `rooted_even_sixteen` at `(q-2,126q+102)`; q=5 mod8 gives a reached positive even first counter with odd second; q=3 mod8 splits by q mod16: residue 3 violates `rooted_one_strong`, while residue 11 forces an impossible positive `(3 mod 4,1 mod 4)` ancestor by `rooted_odd_three_one`. Only q=2 and 7 mod8 remain.

**Verification blocker:** local shell command `container.exec(['bash','-lc','pwd; ls -la | head; date -u +%FT%TZ'])` failed with tool-boundary `ClientError`, as did a trivial `python.exec` command. No Lean diagnostic was available locally. The existing manual `agent18-429-strong-root.yml` has been extended to compile the new file as its final module; it is the smallest existing source slice and should be dispatched once. An accepted local theorem would still require connection through unchanged upstream Cryptids source for an original-machine claim. The source wrapper and last-reset n-parameter arithmetic remain open.

For provenance see `im-results/agent18-429-root-invariants/BB429Branch7Source.lean`, `BB429Branch7.lean` and the 15 November branch-7 memory of Agent18.


## Source-connected exact long-burst reduction (pending upstream-source compile)

The follow-on source module `BB429Branch29Source.lean` composes the six-of-eight rooted exclusion with the unchanged Cryptids `sourceRun` blank-root connector. For branch 7, suppose `n>=18`, `y+3=2x`, `x%32=29`, and the exact final-burst equation `4x+3n+15=3*2^(n+2)` holds at a genuinely source-reachable `(x,y)`. Then the proposed stronger conclusion is

```
n % 1024 = 895 or 1023.
```

Indeed `x=32q+29`, `y=64q+55`, and `q>=21` follows from exponential growth in the exact equation. The original-source/local bridge forces `q%8 in {2,7}`. Since `2^(n+2)` is divisible by 1024 for `n>=18`, the equation becomes `128q+3n+131=0 (mod 1024)`; substituting `q=2,7 (mod 8)` gives `n=895,1023 (mod 1024)`, respectively. This is a genuine source-root *necessary condition*, not a nonhalting decision. The original-source closure is staged in the existing manual `agent6-429-source-chain.yml`; acceptance requires that full source compile and the transitive axiom output, not just the stand-alone local RC2 run.
