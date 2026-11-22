# DR zero-transfer corridor

**Status:** exact local transition lemma; the listed root visits are finite exploratory observations, not an all-time invariant.

## Exact corridor lemma

Write `0^r` for a list of `r` zero tokens. In the outer stack successor system implemented by `fast_root_stack_sim.js`, for all `r ≥ 1` and `b ≥ 0`,

`DR(L = 0^r ++ [1], R = [1] ++ 0^b)`

has the one-step successor

`DR(L = 0^(r-1) ++ [1], R = [1] ++ 0^(b+1))`.

Reason: the `DR` branch sees `L.head = 0` and `R.head = 1`; it drops the left head and prepends `1,0` to the right tail. Thus one zero is transferred from the left stack to the right stack, while the marker `1` remains at the head of `R`.

Iterating exactly `r` times reaches `DR(L=[1], R=[1] ++ 0^(r+b))`. One further `DR` step sees both heads equal to `1` and yields

`CR(L=[0], R=0^(r+b+2))`.

Equivalently,

`S^(r+1)(DR(0^r 1, 1 0^b)) = CR(0, 0^(r+b+2))`.

This is a closed-form compression of a potentially long linear corridor. It does not depend on the rest of either stack because all consumed prefixes are explicit.

## Finite root-trace observations

An exploratory V8 replay of the linked-list successor definitions sampled the following corridor entries (macro indices are zero-based):

| Macro index | r | b | Corridor exit | Exit state |
|---:|---:|---:|---:|---|
| 44 | 7 | 1 | 52 | `CR(L=[0], R=0^10)` |
| 405 | 31 | 1 | 437 | `CR(L=[0], R=0^34)` |
| 3014 | 95 | 1 | 3110 | `CR(L=[0], R=0^98)` |

The entry parameters `7,31,95` are observations only; no recurrence or monotonicity claim is made. The same local lemma can be used to compress any later occurrence once its concrete entry state is established.

## Research use

- Add a corridor detector to the original `fast_root_stack_sim.js` and record the exact entry/exit states directly from that implementation before using these observations in a formal argument.
- Search for a macro-level recurrence governing the next corridor entry parameter `r`; the three observed values are insufficient to infer one.
- Combine the corridor lemma with the existing `Z1` token-normalizer theorem only when the token input is proved to have the required `0^n` or `0^n 1` form.
- This lemma alone does not establish nonhalting, cylinder reachability, or a BB(6) bound.

Source transition definitions: `im-results/agent12-cryptid-root-invariant/fast_root_stack_sim.js`.

## One-million-step cross-check

A 1,000,000-successor V8 replay using the same linked-list transition clauses reproduced the previously recorded terminal summary: mode `CR`, `L=[0,0,1,0,0,0,0,1]`, `|R|=154441`, maximum outer `|L|=268`, maximum `|R|=154446`, and maximum stack entry 203. With the stricter corridor predicate `R = [1] ++ 0^b` (rather than merely `R.head=1` and `|R|=2`), exactly the three sweeps listed above occur in this million-step prefix. The sole token-normalizer call is at macro 21810; its input has length 268 and exactly one `1`, namely `0^267 ++ [1]`. These are finite replay facts, not an infinite-orbit proof.
