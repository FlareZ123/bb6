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

The Lean `tower(0,b)=b`, `tower(n+1,b)=2^(tower(n,b))-1` and **corrected** `sumTower(0,b)=b`, `sumTower(n+1,b)=sumTower(n,b)+tower(n+1,b)` now match the original Rocq `t2` and `st2` literally. For any positive `b`, the Lean kernel establishes `sumTower(n,b)%2=(b+n)%2` without evaluating the astronomical tower. An initial draft incorrectly used `sumTower(0,b)=0` and asserted the generally false parity formula `n%2`; this was corrected on 2026-11-03 after re-reading source `st2`. The present genuine exponent uses `b=6`, so its parity and the subsequent halting residue conclusion are unchanged. Do not reuse the superseded general formula.

The authentic Rocq prefix `init` gives `S1(3,7,m2,6,0,63)`. `Rsts1` yields an `m1` configuration with `a=sumTower(7,6)+12`, which is odd. Lean theorem `published_blank_gate` establishes that the first reset has index 1 modulo 3 and the second reset has index 2 modulo 3 **for the enormous actual next exponent `tower(8,6)`**. This reconstructs the modular core of the existing Rocq proof without attempting to evaluate the giant number. It is a transparent check of previously established halting reasoning, not a novel champion decision.

## Verification and limits

Run `lean im-results/agent24-champion-time/ChampionModular.lean` under Lean **4.36.0-rc2**. Local run on 2026-11-03 was successful with `#print axioms published_blank_gate` returning `[propext, Quot.sound]` and no `sorryAx`. The theorem is **arithmetic about the published formulas**, with no local `TM63.S1` tape definition or imported Coq proof; only the original Rocq module supplies the machine-to-macro semantic link.

Crucially the original `TM63.halt` and the intermediate `-->*` statements give existence of finite paths, **without explicit counted primitive steps**. Neither this modular classification nor the Agent48 exact six-step root join provides a numerical theorem `HaltsAfter championTable N`. It would be unsound to treat the previously published approximate tower scale as a proved exact score. The global maximum proof also still lacks the universal six-state upper bound.

## Concrete next proof edge

For an exact champion step score, strengthen the source macro chain `LC_Inc` / `Incs0` / `Rst2` / `Rst1` / `Rst0` / `Rst1'` / `Rsts1_v2` / `Rsts2H` to produce **primitive-step counts** alongside endpoint configurations. Compose these into an executable symbolic recurrence for the existing finite macro itinerary and check the start/root and final halting-query conventions against `BB6Coverage.HaltsAfter`. A source-certified finite numerical expression would supply an attainable lower bound, with global upper-bound completeness still separate. No such counted source proof is claimed here.

All novelty, source integration and universality claims remain deliberately qualified; this file is under `im-results/`.

## New primitive-step cost conjectures (finite evidence only)

The executable [`verify_counted_macros.py`](verify_counted_macros.py) uses the literal original 12 TM63 transition entries with a finitely supported bi-infinite tape. It interprets the original `TM63.S1` convention carefully: in Coq, `l <{{D}} r` places the head on **the last cell of the physical left word**, whereas the first cell of `r` is its right neighbor. Getting that offset wrong causes spurious failed macro matches. With the corrected convention, the raw blank-root simulator reaches the published `S1(3,7,m2,6,0,63)` **exactly after 27,959 ordinary transitions**.

Independent primitive-step simulation suggests three concise *all-parameter conjectures*. Let `v₂(n)` denote the number of trailing zero bits of positive `n`, and let `m=0,1,2` index the source's `Rst0/Rst1/Rst2` middle marker. For source transitions from `S1(L,n,m,a,0,b)`, with `1≤n<2^L`, to their exact published `S1` successor:

```text
C_increment(m,n,a,b) =
    6*4^b + 42*2^b - 9*b + 15 + 4*m + 12*(a + v₂(n))

C_reset_core(L,a,b) = 97 + 12*(L+a) + 3*b
C_reset_drain(b)    = 6*(4^b-1) + 42*(2^b-1) - 12*b
C_Rst1'(L,a,b)     = 12*(L+a) + 6*4^b + 42*2^b - 9*b + 49

C_Rst0'_to_halt_query(L,a,b) = 59 + 12*(L+a)
```

The `Rst1'` decomposition follows the **actual intermediate configuration** visible in its pinned Rocq proof: `S1(L+a+2,R(L,a),m2,b,2^b-1,0)`. The first formula's target is `S1(L,n-1,m',a+b+δ,0,2^b−1)`, where `m'` cycles 2→1→0→2 and `δ=1` for `m=0`, `δ=2` otherwise. The final formula counts successful transitions **up to**, and excluding, the undefined halting query. One must separately reconcile whether the external Busy Beaver scoring convention counts the terminal halt action.

All source-authentic endpoint configurations were compared by **complete finite set of marked cells relative to the head**, without fingerprints or approximate observations. Running the checked-in deterministic script locally on 2026-11-03 produced:

```text
INIT: 27,959 exact nonhalting blank-root moves to published S1
INC: 2860 finite original-step trials
RESET: 252 exact finite core/drain/composition trials
TERMINAL: 300 finite halt-query trials
ALL FINITE TESTS PASS; these do not establish quantified formulas.
```

The 2,860 increment checks cover all three markers, `L=1..6`, `1≤n<min(2^L,18)`, `a∈{0,1,3}`, `b=0..4`, and 160 pseudorandom extra instances with fixed seed `20261103`. The reset checks cover `L,a=0..5,b=0..6`; terminal checks `L,a=0..9,b∈{0,1,7}`. A separate exploratory experiment matched `Rst1'` for `b=0..11`, including a 25,251,790-step instance.

**Evidence class: finite computational conjecture.** Endpoint agreement for 3,412 instances is a substantial hint about a reusable exact raw-step cost model, but proves nothing for unrestricted `n,L,a,b`. The Lean file above certifies the source's modular gating arithmetic only. The proposed time formulas have **no universally quantified Lean or Coq proof**, no verified cross-language semantics transport, and supply **no certified numerical champion score**. Future research should first prove the 59+12(L+a) terminal and 97+12(L+a)+3b reset-core macros symbolically; then prove the v₂(n) carry-law and the geometric drain-cost recurrence. The latter has observed difference `C_drain(b+1)-C_drain(b)=18*4^b+42*2^b-12`, a natural induction target. Only then should costs be composed over the champion's massive macro itinerary.

## Formal closed form for the proposed binary drain and new micro-step test

A narrower raw-step experiment extracts the original `Inc0` decrement from a general `S1(L,n,m,a,z,c)` with `1 ≤ z < 2^a`. Its apparent primitive-step cost is
```text
C_Inc0_micro(z,c) = 48 + 12*v₂(z) + 12*c
```
and its exact endpoint is `S1(L,n,m,a,z-1,c+1)`, with unchanged physical left context. This was tested against all twelve real TM63 raw actions on **1,000 additional seeded random finite configurations** with varying `L,n,m,a,z,c`, and all tests matched. The extended [Python harness](verify_counted_macros.py) now exercises 4,412 finite instances across the complete set of macro families.

We also extracted the **fully proved arithmetic component** into [`CountPattern.lean`](CountPattern.lean). Its structural valuation word is
```text
carryPattern(0)   = []
carryPattern(b+1) = carryPattern(b) ++ [b] ++ carryPattern(b).
```
For `charge([v₁,...,v_N],0)=Σᵢ[48+12*vᵢ+12*(i-1)]` and `drainPattern(b)=charge(carryPattern(b),0)`, Lean 4.36.0-rc2 proves **universally**, without `sorry` or nonstandard axioms:
```text
carryPattern(b).length + 1 = 2^b
carryPattern(b).sum + b + 1 = 2^b
drainPattern(b) + 12*b + 48 = 6*4^b + 42*2^b.
```
The last theorem is `BB6ChampionArithmetic.drainPattern_closed`, checked by the actual Lean kernel; `#print axioms` reports only `[propext, Quot.sound]`. This explains the observed exponential drain *arithmetically* as the binary carry pattern accumulated by sequential decrements. Its proof is independent of any machine-level assumption. **The missing theorem remains that each physical TM63 `Inc0` micro-transition obeys the proposed time formula and that its valuation sequence exactly matches `carryPattern(b)`.** The count is not yet source-certified as TM runtime.

The micro-step conjecture suggests a particularly economical next formalization: prove a complete raw-machine `S1` binary-decrement lemma parameterized by a trailing run of zero digits, then obtain the general `Inc0` time by a case split on `v₂(z)`, and finally apply the Lean-proved `drainPattern_closed` to the already-known source decomposition `Rst1'` and `Rsts0/1/2`. This would turn the observed huge cost pattern into a rigorous primitive-step theorem with no astronomical simulation.
