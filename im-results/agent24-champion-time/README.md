# Champion-family reset arithmetic: kernel-checked intermediate

**Agent 24, 2026-11-03, R005.** Mathematical arithmetic facts were checked in Lean 4.36.0-rc2. The Lean file [ChampionModular.lean](ChampionModular.lean) requires only `Lean.Elab.Tactic.Omega`, no mathlib, axioms, `sorry`, or replacement machine semantics. This is **not** a new BB(6) bound, champion step-count certificate, rooted-machine decision, or a source-integrated Coq-to-Lean proof.

## Original source and exact formulas

Compare the actual published [Rocq `TM63` source at pinned revision `3f302b87...`, `verify/SOBCv5.v` lines 10750–11283](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10750-L11283). The table is `1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`. The original theorem `TM63.halt : halts tm c0` is an **existential halting proof**. See the separately source-verified [Agent48 champion-root six-step bridge](../agent48-champion-root/README.md) and [Agent42 two-cylinder coverage programme](../agent42-coverage-normal/README.md).

The published `Rst1'` macro is

```text
S1(L, 0, m1, a, 0, b)
  -->* S1(L+a+2, (4*2^L-1)*2^a-1, m2, b, 0, 2^b-1).
```

The new middle index is `R(L,a)=(4*2^L-1)*2^a-1`. `Rst1'_WF` establishes `R(L,a)<2^(L+a+2)`, so the next macro is applicable. `Rsts2H` proves halting when the `m2` index is congruent to 2 modulo 3. If it is congruent to 1, `Rsts1_v2` reaches another `m1` reset with the **same** length `L+a+2`.

## Complete three-case modular classification

The Lean file proves **for all natural** `k,a`:

```text
R(2k,   a)    % 3 = 2
R(2k+1, 2a)   % 3 = 0
R(2k+1, 2a+1) % 3 = 1
```

In the third case the next reset length `(2k+1)+2+(2a+1)=2(k+a+2)` is even. Consequently, composing the *already published* source lemmas gives the following mathematical sufficient halting region:

**Every physical `TM63.S1(L,0,m1,a,0,b)` halts whenever `L` is even or `a` is odd.** Even `L` terminates via one `Rst1'` and `Rsts2H`; odd `L` plus odd `a` takes `Rst1'`, `Rsts1_v2`, a second `Rst1'`, then `Rsts2H`. The parity-sector `L` odd and `a` even has residual index 0 modulo 3, so this argument makes **no claim** there. The Coq macro statements carry the necessary preconditions; this composition has not been added as a separately compiled Coq theorem.

The Lean `tower(0,b)=b`, `tower(n+1,b)=2^(tower(n,b))-1` and `sumTower(0,b)=0`, `sumTower(n+1,b)=sumTower(n,b)+tower(n+1,b)` are **syntactically the same definitions** as the original Rocq `t2` and `st2`. Note that the wiki's informal written `st2` inclusive summation differs from the source base case; the source implementation controls this audit. For any positive `b`, the kernel establishes `sumTower(n,b)%2=n%2` without evaluating the astronomical tower.

The authentic Rocq prefix `init` gives `S1(3,7,m2,6,0,63)`. `Rsts1` yields an `m1` configuration with `a=sumTower(7,6)+12`, which is odd. Lean theorem `published_blank_gate` establishes that the first reset has index 1 modulo 3 and the second reset has index 2 modulo 3 **for the enormous actual next exponent `tower(8,6)`**. This reconstructs the modular core of the existing Rocq proof without attempting to evaluate the giant number. It is a transparent check of previously established halting reasoning, not a novel champion decision.

## Verification and limits

Run `lean im-results/agent24-champion-time/ChampionModular.lean` under Lean **4.36.0-rc2**. Local run on 2026-11-03 was successful with `#print axioms published_blank_gate` returning `[propext, Quot.sound]` and no `sorryAx`. The theorem is **arithmetic about the published formulas**, with no local `TM63.S1` tape definition or imported Coq proof; only the original Rocq module supplies the machine-to-macro semantic link.

Crucially the original `TM63.halt` and the intermediate `-->*` statements give existence of finite paths, **without explicit counted primitive steps**. Neither this modular classification nor the Agent48 exact six-step root join provides a numerical theorem `HaltsAfter championTable N`. It would be unsound to treat the previously published approximate tower scale as a proved exact score. The global maximum proof also still lacks the universal six-state upper bound.

## Concrete next proof edge

For an exact champion step score, strengthen the source macro chain `LC_Inc` / `Incs0` / `Rst2` / `Rst1` / `Rst0` / `Rst1'` / `Rsts1_v2` / `Rsts2H` to produce **primitive-step counts** alongside endpoint configurations. Compose these into an executable symbolic recurrence for the existing finite macro itinerary and check the start/root and final halting-query conventions against `BB6Coverage.HaltsAfter`. A source-certified finite numerical expression would supply an attainable lower bound, with global upper-bound completeness still separate. No such counted source proof is claimed here.

All novelty, source integration and universality claims remain deliberately qualified; this file is under `im-results/`.
