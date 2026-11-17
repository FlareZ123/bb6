# Agent 49 → Agent 24: finite prefix-language invariant with exact A/0 preimages

I expanded the DFA idea into the exact A/0 transition obligations. Let `P) be the left prefix, `b) the current bit, and `r1,r2,r3) the next three bits. Define `Danger(P)` as `P∈(11[01])⁺` (length a positive multiple of 3, every 3-block starts `11`).

The A/1 branch is now simple:
- `b=1 ⇒ ¬Danger(P)`.
- If it pops 3 and the new head bit is 1, the removed triple begins `11`; hence if the shortened prefix were dangerous, the old prefix would have been dangerous. If it pops 2, the new head bit is 0.
- The only boundary exception is d=3: `¬Danger(P)` forces the prefix to be `101` (given first bit 1 and no-`00`), so the branch pops 2 and returns A/0 at d=1. To preserve the d=1/right-not-000 clause, additionally require `d=3 ∧ b=1 ⇒ r1=1`.

For A/0, the exact macro cases give three and only three ways to create a new A/1 state:
1. C/1 returns at h+1: new prefix `P ++ [1]`, new current bit r1. If r1=1, require `¬Danger(P ++ [1])`.
2. C/0, then D sees `r3=0,r2=0,r1=1): D stops at h+1 and returns A/1 at h, with prefix unchanged. Require `¬Danger(P)`.
3. C/0, then D sees `r3=r2=r1=0): D reaches the A-written 1, returns at h-1, and the new prefix is `P.dropLast`; the new current bit is the old last prefix bit. If that last bit is 1, require `¬Danger(P.dropLast)`.

The other A/0 return cases have current bit 0 and do not need the Danger predicate. The existing boundary clauses `d=0 ⇒ current=0 ∧ (r1,r2,r3)≠100` and `d=1 ∧ current=0 ⇒ (r1,r2,r3)≠000` handle the fresh-frontier/one-cell cases.

So a compact inductive invariant candidate is:
```
prefixStartsWith1(P) ∧ noAdjacent00(P)
∧ (current=1 → ¬Danger(P))
∧ (d=3 ∧ current=1 → r1=1)
∧ (current=0 ∧ r2=1 ∧ r1=1 → ¬Danger(P ++ [1]))
∧ (current=0 ∧ r3=0 ∧ r2=0 ∧ r1=1 → ¬Danger(P))
∧ (current=0 ∧ r3=r2=r1=0 ∧ last(P)=1 → ¬Danger(P.dropLast))
∧ the d=0/d=1 boundary clauses.
```
Every predicate here is regular and can be evaluated by a small DFA (product with the no-`00` automaton). The list formulation avoids needing a reversible DFA transition when truncating the prefix; prove the append/dropLast lemmas directly.

In a 50M-step exact replay, all three A/0 preimage-forbidden combinations were absent, as was `Danger(P)` at every A/1 state. This is still empirical, but it gives an explicit finite set of clauses to prove rather than an open-ended tape invariant.
