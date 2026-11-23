# Cryptids #429: rooted 29-mod-32 odd-reset inverse restriction

**Status:** The uniform q mod8 theorem is Lean 4.36.0-rc2 accepted in [CI 45108772982](https://github.com/FlareZ123/bb6/actions/runs/45108772982), with transitive axioms [propext, Classical.choice, Quot.sound] and no sorryAx. The subsequent original-source and deeper mod16 refinements await their respective compiler audits. All are intermediate restrictions, **not** an exact #429 or BB(6) decision.

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


## New residual refinement: q modulo 16

`BB429Branch29Mod16.lean` is a further uniform inverse argument, *Lean-verified in [CI 45109428286](https://github.com/FlareZ123/bb6/actions/runs/45109428286), axioms [propext, Classical.choice, Quot.sound]*. It sharpens the preceding q mod8 theorem to

```
q%16 in {2,10,15}, or q=55
```

for every q>=21 at a true-blank accelerated `(32q+29,64q+55)`. On the q=16r+7 sector, the first seven exact ancestors reach `(4r-1,2040r+990)`; when r!=3 (i.e. q!=55), its two possible source parents have positive-even first counter and odd second, except for r=1's zero/odd parent, which the `Allowed` invariant excludes. At r=3, the target first counter is 11, where exceptional source inverses invalidate the two-parent argument. This finite index is explicitly preserved rather than dropped. The original infinite q%16=7 cylinder is thus excluded except one named finite candidate. This remains an intermediate (not whole #429) theorem even if the RC2 compile succeeds.

## Finite exceptional q=55 (in compiler preflight)

`BB429FiniteAvoidance.lean` proves soundness of an arbitrary-target Boolean prefix verifier, and a global nonreachability rule whenever the certified prefix ends at a rank larger than the target rank. It supplies a 1586-step exact prefix for the actual root, ending at `(3069,996)`, rank 7134, avoiding `(11,7110)` of rank 7132. Both computational facts use ordinary kernel reduction via `decide`, not `native_decide`. `BB429Branch29Mod16.no_29_q55` proves a q=55 source ancestry would require the forbidden `(11,7110)` state. If the new CI compile succeeds, `rooted_29_q_three_mod16` yields the clean all-q>=21 necessary condition `q%16 in {2,10,15}`, excluding 13 of 16 parameter residues. The q55 closure and clean statement must remain *unaccepted* until this focused CI check and axiom report succeed.
