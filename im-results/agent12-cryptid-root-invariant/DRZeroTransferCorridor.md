# DR zero-transfer corridor

**Status:** exact local transition lemma; the listed root visits are finite exploratory observations, not an all-time invariant.

## Exact corridor lemma

Write `0^r` for a list of `r` zero tokens and let `T` be an arbitrary finite right-list tail. In the outer stack successor system implemented by `fast_root_stack_sim.js`, for all `r ≥ 1`,

`DR(L = 0^r ++ [1], R = [1] ++ T)`

has the one-step successor

`DR(L = 0^(r-1) ++ [1], R = [1,0] ++ T)`.

Reason: the `DR` branch sees `L.head = 0` and `R.head = 1`; it drops the left head and prepends `1,0` to the right tail. Thus one zero is transferred from the left stack to the right stack, while the marker `1` remains at the head of `R`. Crucially, **no condition on `T` is needed**.

After exactly `r` such steps, the state is `DR(L=[1], R=[1] ++ 0^r ++ T)`. One further `DR` step sees both heads equal to `1` and yields

`CR(L=[0], R=0^(r+2) ++ T)`.

Equivalently, for all `r ≥ 0` and arbitrary `T`,

`S^(r+1)(DR(0^r 1, 1 ++ T)) = CR(0, 0^(r+2) ++ T)`.

This is a closed-form compression of a potentially long linear corridor. It does not depend on the rest of either stack because all consumed prefixes are explicit.

## Finite root-trace observations

An exploratory V8 replay of the linked-list successor definitions observed these all-zero-tail examples (macro indices are zero-based):

| Macro index | r | T | Corridor exit | Exit state |
|---:|---:|---|---:|---|
| 44 | 7 | `[0]` | 52 | `CR(L=[0], R=0^10)` |
| 405 | 31 | `[0]` | 437 | `CR(L=[0], R=0^34)` |
| 3014 | 95 | `[0]` | 3110 | `CR(L=[0], R=0^98)` |

The entry parameters `7,31,95` are observations only; no recurrence or monotonicity claim is made. The generalized lemma also applies to corridor states with nonzero `T`; the table is not an exhaustive list of all occurrences.

## Research use

- Add a corridor detector to the original `fast_root_stack_sim.js` and record exact entry/exit states directly from that implementation before using finite observations in a formal argument.
- Search for a macro-level recurrence governing the next corridor entry parameter `r` and tail `T`; the three all-zero-tail examples are insufficient to infer one.
- Combine the corridor lemma with the existing `Z1` token-normalizer theorem only when the token input is proved to have the required `0^n` or `0^n 1` form.
- This lemma alone does not establish nonhalting, cylinder reachability, or a BB(6) bound.

Source transition definitions: `im-results/agent12-cryptid-root-invariant/fast_root_stack_sim.js`.

## One-million-step cross-check

A 1,000,000-successor V8 replay using the same linked-list transition clauses reproduced the previously recorded terminal summary: mode `CR`, `L=[0,0,1,0,0,0,0,1]`, `|R|=154441`, maximum outer `|L|=268`, maximum `|R|=154446`, and maximum stack entry 203. Exactly three sweeps with the special tail `T=[0]` occur in this million-step prefix, at the entries listed above. The sole token-normalizer call is at macro 21810; its input has length 268 and exactly one `1`, namely `0^267 ++ [1]`. These are finite replay facts, not an infinite-orbit proof.