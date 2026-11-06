# #623: sharp ternary-budget translations of the complete accelerated return

**Research status:** the sharp ternary-budget translation and its new affine-buffer theorem are compiled against the unmodified original DeepMind source in pinned GitHub Actions run [42245913367](https://github.com/FlareZ123/bb6/actions/runs/42245913367), using upstream-required Lean 4.35.0-rc4 and the pinned source SHA below. The source CI passed all compilation and axiom-audit steps. This result determines neither the machine's blank-origin fate nor BB(6).

## Mathematical claim

For the two-symbol six-state machine `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, write `E(a,k,m)` for the original DeepMind evaluator `evalA`, `B(a,b,d)` for `drainB`, and `T(D(a,d))` for `highLevelNext`. Let `u_a=(3^a-1)/2`, the base-3 integer with `a` digits equal to one.

For every `a,b,d,t : Nat` with `b≤u_a`:

```text
B(a+t,b,d) = Option.map (D(·+t,·)) (B(a,b,d)).
```

This identity includes `t=0` and all finite first counters. The domain is **sharp as a uniform initial interval**: at `b=u_a+1`, `B(a,b,d)=none` while `B(a+1,b,d)` is successful, for every `a,d`. The evaluator obeys the corresponding identity under `k<u_a`:

```text
E(a+t,k,m) = Option.map ((x,y,z) ↦ (x+t,y,z)) (E(a,k,m)).
```

The earlier source-proved `b<a` first-counter translation of Agent 8 is extended to an exponential budget in `a`. This can substantially reduce the required first-counter slack in inverse computations.

## Four extended high-level affine sectors

The identity transfers to four complete source-matched transition branches, with `T` and `D` as above.

| Input sector | Hypotheses | Exact output translation |
| --- | --- | --- |
| Far-left, odd `d` | `d%2=1`, `a≥d+5`, `d+3≤u_(a-d-5)` | `T(D(a+t,d))=shift_t(T(D(a,d)))` |
| Far-left, even `d` | `d%2=0`, `a≥d+3`, `d+2≤u_(a-d-2)` | `T(D(a+t,d))=shift_t(T(D(a,d)))` |
| Far-right, odd `d` | `a>0`, even `a`, `a≤d`, `a-1≤u_(d+4-a)` | `T(D(a,d+2t))=shift_(2t)(T(D(a,d)))` |
| Far-right, even `d` | `a>0`, even `a`, `a≤d`, `a<u_(d+1-a)` | `T(D(a,d+2t))=shift_(2t)(T(D(a,d)))` |

All four statements are proved in the same local source-matched Lean compilation. For example, with `d=101, a=112`, the first left sector applies because `104≤u_6=364`, although the old `a>2d+8` condition fails. Exact computation gives `T(D(112,101))=D(6,321)`, `T(D(113,101))=D(7,321)` and `T(D(114,101))=D(8,321)`. This example is a check of the general theorem, not its proof.

## Proof and provenance

The evaluator proof inducts on `a`. At ternary residual digit 2 or 0 the output shifts immediately; at digit 1, the inequality `k<u_(a+1)=3u_a+1` entails `k/3<u_a`, enabling induction. The drain theorem uses well-founded strong induction on `b`, the previously established exact `evalA_ones_budget` invariant and `evalA_b_le_k`. Each successful evaluator step decreases the current `b` and preserves the `u_a` budget for the recursive call. Sharpness is a consequence of source-proved `drainB_first_halt` and `drainB_safe_ones`. The high-level sector proofs expand the actual branch guards and compose these two identities.

- **Prior standalone verification:** an earlier invocation compiled a source-matched arithmetic model with Lean **4.36.0-rc2**, with no errors, `sorry`, or custom axioms. The source-imported CI proof below is the durable verification. `#print axioms` for all seven new claims printed exactly `[propext, Quot.sound]`. That temporary file copies the arithmetic transition rules and is **not in this repository**; the durable source-port proof is below.
- **Source-import proof port:** [TernaryShiftSource.lean](TernaryShiftSource.lean) imports [Parity623Source.lean](Parity623Source.lean), which imports the unchanged original Cryptids source [at pinned SHA `c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean). [Manual CI workflow](../../.github/workflows/agent49-623-ternary-shift.yml) compiles the true upstream file, the parity module, the exponential budget dependency, the translation module and the affine-buffer module. [Source-pinned run 42245913367 passed](https://github.com/FlareZ123/bb6/actions/runs/42245913367). The follow-on buffer proof initially failed because the translation module had not been emitted as an `.olean`; the workflow now explicitly emits it before compiling the dependent module.
- **Previous baseline:** [Agent 8's original-source first-counter translations](../agent8-623-inverse/TernaryFirstSource.lean) require the linear `b<a` bound for the drain; their far-left condition is about `a>2d` rather than `a≈d+O(log d)`. [Our prior exponential safety theorem](Parity623Source.lean) establishes survival but does not, by itself, prove affine outputs.

## Open obligations

The source-imported translation and buffer proofs now pass their pinned CI and ordinary axiom audits. Next, use the four affine sectors to classify authentic blank-root predecessors of the remaining narrow halting corridor. Synthetic affine rays alone do not establish that any of their states are reachable from `D(0,7)`. The original machine's halting status and the BB(6) upper-bound/coverage problem both remain unresolved.


## Source-verified affine buffer theorem

The companion [TernaryBufferSource.lean](TernaryBufferSource.lean) extends the translation identities into a one-step output classification. Let `u_n=(3^n-1)/2`. It defines four exponential sectors:

```text
newAffineCone(a,d) :=
  (d odd,  d+5 ≤ a, d+3 ≤ u_(a-d-5))
  OR (d even, d+3 ≤ a, d+2 ≤ u_(a-d-2))
  OR (a>0 even, a≤d, d odd,  a-1 ≤ u_(d+4-a))
  OR (a>0 even, a≤d, d even, a   < u_(d+1-a)).
```

The four older linear sectors are contained in this exponential cone:

```text
oldAffineCone(a,d) :=
  (d odd,  2d+8 < a)
  OR (d even, 2d+4 < a)
  OR (a>0 even, d odd,  2a+1 ≤ d)
  OR (a>0 even, d even, 2a+2 ≤ d).
```

The principal theorem `newAffine_to_oldRight` proves, for every even `a), every state in `newAffineCone` but outside `oldAffineCone`, apart from the two explicit exceptions `(a,d)=(4,5)` and `(4,7)), and every successful return `T(D(a,d))=D(b,e)), that

```text
b is even  AND  2*b+1 ≤ e.
```

Thus every covered output lies in the old strong-right sector. Its proof combines the source-matched first-counter translation, the B-drain first-counter upper bound, the third-counter growth bound, and finite certificates for the small right-sector boundary. The CI log reports only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appears.

**Reachability limitation:** this is a universal theorem about a class of synthetic section states and their successful successors. It does not show that the blank-origin orbit stays in the class, does not classify the old linear sectors' successors, and does not decide either of the two excluded synthetic inputs. In particular, it is not a proof that machine #623 does not halt.
