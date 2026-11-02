# Agent 23: exact infinite Machine C reset-gateway exclusion (j = 3 modulo 16)

**Status:** All-time symbolic Lean proof locally compiled under Lean 4.36.0-rc2, using standard axioms only, with an independent exact-definition bridge to Agent 11's Machine C acceleration. This is a genuinely infinite reachability exclusion. **This note is intermediate pending independent CI compilation against the repository's unmodified `CLine.lean` and prior-art review; it does not decide Machine C or BB(6).**

Machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. The original blank-tape machine enters `(5,0,1)` under the published Google DeepMind acceleration, and its machine-to-accelerator equivalence was separately certified in Agent 21's pinned-upstream CI run [41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481).

## Main theorem

For every natural `t`, the original copied accelerator cannot reach the reset-gateway family at index `j=16t+3`:

```lean
theorem BB6.Agent23.source_reset_three_mod_sixteen_unreachable (t : Nat) :
    ¬BB6CLine.Reach (32*t+7,48*t+13,0)
```

Here `(32t+7,48t+13,0)=(2j+1,3j+4,0)`. This class had appeared in Agent 20's computational modulo-64 overapproximation but had not been directly kernel-certified in that investigation. There is no blanket exclusion of the other gateway classes.

## Pure symbolic argument

Let `Reach` denote finite reachability from `(5,0,1)` under the nine-case exact map. Independently proved backward structural lemmas yield:

1. Every reachable `(a,k+3,c+4)` has the unique high-stage predecessor `(a+1,k+2,c+5)`. Iterating this statement gives a parameterized high-sector strip to middle coordinate `2`.
2. Every reached reset `(a,k+6,0)` forces a reached high hub `(a+k+1,2,k+4)`.
3. A reached high hub `(a,2,c+4)` with `a%4≠2` forces `(a+1,1,c+5)`. A reached `(a,1,c+4)` forces either the positive-high predecessor `(a+1,0,c+5)` or a zero-right predecessor `(a+2,q,0)` with `c+4=2q+1`.
4. The reached `(a,0,c+4)` states satisfy `a%4=1`. For `a≥5`, they must have arisen via the odd zero-left high branch, so their predecessor is `(0,q,c+4)` for odd `q` with `a=4*(q/2)+5`.
5. A separately established and locally re-proved all-time stage invariant implies `Reach(A,K,0)` and odd `K≥5` entail `(A+K)%4∈{0,3}`.

Assume the indexed reset `(32t+7,48t+13,0)` were reached. Reverse three compulsory sections and strip the high middle counter to reach `(80t+15,2,48t+11)`, then `(80t+16,1,48t+12)`. The zero-right parent possibility has an even third counter and is impossible, so the chain forces `(80t+17,0,48t+13)`. Its odd zero-left high predecessor is `(0,40t+7,48t+13)). Strip that high stage again to reach `(40t+5,2,88t+18)`, then `(40t+6,1,88t+19)`.

At this last state, the positive-high predecessor would have left counter `40t+7≡3(mod4)` at middle counter zero, contradicting (4). The other possible predecessor is `(40t+8,44t+9,0)`. Its middle counter is odd and at least five, but the sum is `84t+17≡1(mod4)`, contradicting (5). This proves exclusion for all `t` without simulation bounds.

## Verification and reproduction

`CM16.lean.xz.b64` stores the 13,422-byte full original Lean source. Run `python reconstruct.py` to restore and SHA-256-check it. The expected source hash is `d8ea25e4a62b5f2fe7211d7bdef1b58af6193501daf54797e10d290ed24ad516`. The reconstruction script uses `filelock` for atomic locked writes. `CMod16Bridge.lean` imports `CM16` and `CLine`, proves the two next-step functions definitionally equal with `rfl`, transports every reachable state to the local predicate, and states the exact theorem above.

Local Lean 4.36.0-rc2 compiler checks reported for both final theorems `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**. The next verification gate is the manually dispatched `.github/workflows/agent23-c-mod16.yml` with the repository's full, unmodified `im-results/agent11-c-line/CLine.lean`. The original-machine source-level link is the previously checked Agent 21 bridge. This proof does not establish global nonhalting; substantial surviving reset and side gateway classes remain unresolved.
