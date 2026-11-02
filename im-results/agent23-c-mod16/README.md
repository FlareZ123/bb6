# Agent 23: exact infinite Machine C reset-gateway exclusion (j = 3 modulo 16)

**Status:** All-time symbolic Lean proof **independently verified** under Lean 4.36.0-rc2 against the repository's complete unmodified Agent 11 source in [successful manually dispatched GitHub Actions run 41398279064](https://github.com/FlareZ123/bb6/actions/runs/41398279064), using standard axioms only. This is an infinite reachability exclusion, previously suggested computationally by Agent 20. It does not decide Machine C or BB(6).

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

Local Lean 4.36.0-rc2 compiler checks reported for both final theorems `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**. The manual independent proof gate **passed** in [run 41398279064](https://github.com/FlareZ123/bb6/actions/runs/41398279064), against commit `5a26556d4d094d2f9e327f8339dbed9f2b26a9b3`, including the unmodified `im-results/agent11-c-line/CLine.lean`. The original-machine source-level link is the previously checked Agent 21 bridge. This proof does not establish global nonhalting; substantial surviving reset and side gateway classes remain unresolved.

## Two further exact infinite-family symbolic certificates (2026-11-02)

### Reset j = 64t+7

`C7.lean` proves `reset_seven_mod_sixtyfour_unreachable` and `C7Bridge.lean` transports the theorem to the unmodified Agent11 `Reach`:

```lean
∀ t : Nat, ¬BB6CLine.Reach (128*t+15,192*t+25,0)
```

For each target, compulsory reverse reset and high-sweep transitions reduce reachability to `(320t+36,1,192t+24)` and then `(0,160t+17,192t+25)`. A further high strip leads to `(160t+16,1,352t+41)`. Its high predecessor is ruled out by the residue of the zero-middle left counter. The zero-right predecessor, `(160t+18,176t+20,0)`, has a second forced reset strip leading to `(336t+34,1,176t+19)`. Again the high predecessor violates the zero-middle residue and the zero-right alternative `(336t+36,88t+9,0)` violates the odd-zero modular hole because the counter sum is `424t+45≡1(mod4)`.

**Independent complete source CI success:** [run 41398872656](https://github.com/FlareZ123/bb6/actions/runs/41398872656), commit `d55282c1949bfef8649e0ad55f92a236013fba35`, final axiom audit only `[propext, Classical.choice, Quot.sound]`.

### Reset j = 64t+59

`C59.lean.xz.b64` stores the 5,848-byte proof, restored via the same atomic SHA256-verifying `reconstruct.py`. Expected hash: `12828c07852c20734f342347b32ef3b15b6e6f2307b1a2f2c48193a0303e7543`. `C59Bridge.lean` proves:

```lean
∀ t : Nat, ¬BB6CLine.Reach (128*t+119,192*t+181,0)
```

The additional `reached_two_split` lemma exhaustively handles a high hub with left counter `a+6`: its earlier state is either `(a+7,1,c+5)` or an even-middle zero-left high-branch portal `(0,k,c+7)` with `a+6=4*(k/2)+2`. This permits multiple alternations of backward sections. The chain from the reset reaches `(160t+146,1,352t+327)`; its surviving zero-right branch forces `(336t+306,2,176t+161)`. The high predecessor of this hub violates the zero-middle residue, while the portal forces `(0,168t+152,176t+164)` and then `(168t+150,2,344t+314)`. The high branch here reaches a forbidden odd-zero modular hole `(168t+153,172t+157,0)`. Its portal branch forces `(0,84t+74,344t+317)`, and further reversal forces `(84t+73,1,428t+390)`, whose two parents are both impossible. All branch eliminations are symbolic, for arbitrary `t`.

**Independent complete source CI success:** [run 41399415330](https://github.com/FlareZ123/bb6/actions/runs/41399415330), commit `2146876b9e31f8efeaa65241fe901ecc086d42a1`, final axiom audit only `[propext, Classical.choice, Quot.sound]`.

The previously known Agent 20 mod64 finite quotient suggested both of these families computationally. These proof files supply direct reusable all-time Lean certificates against the full original accelerated map. No general Machine C halting decision follows.
