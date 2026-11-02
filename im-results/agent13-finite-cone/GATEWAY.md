# P1 exceptional odd-counter gateway: an exact Diophantine classification

**Status: verified mathematical intermediate statement, no blank-tape holdout decision.**

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, reduced to `G` and `T` in the independently published, machine-certified Google DeepMind Cryptids source:
https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean

The complete source `BadGateway.lean` imports `FiniteCone.lean`, which restates the literal published `G,T` maps. Reconstruct using `python unpack.py` and `python unpack_gateway.py`; compile the base module to `FiniteCone.olean`, then compile `BadGateway.lean` with the module available in Lean's search path (Lean 4.36.0-rc2, bundled `Std`). The compressed gateway source SHA256 is verified against its *uncompressed* checksum `569c746b9c2a29d71de962482a74ac5b150cfa52f9dce5aff0fa4775b62e8aac`. The proof compiled locally, and `#print axioms` shows standard `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`, no `sorryAx` or native execution axioms.

## Exact classification

For **every** natural `k` and **positive even** `d≥2`:
```text
((G(k,d)).first % 8 = 0 AND (G(k,d)).second = 3)
    IFF
2*k = 3*d.
```

This is kernel-checked as `G_even_bad_iff`. Equivalently, since a positive even-counter `T` excursion from even `a` and even `c≥6` takes two steps to `G(a/2+2,c-4)`, a return with second counter `3` and first counter divisible by `8` occurs **if and only if**
```text
3*c = a + 16.
```

This is `T_even_bad_gateway_iff`, with the exact two-step map separately proved as `T_two_even`.

Proof mechanism: on the first recursive `G` step, the input `d` even becomes `2d+3 ≡ 3 (mod 4)`. If it recurses twice, the new input is `4d+9 ≡ 1 (mod 4)`; a separate all-input modular lemma forces any `c=3` output thereafter to have first counter congruent **4 modulo 8**. In the nonrecursive cases, the middle exit cannot return `c=3`, and the immediate high exit returns it precisely when the one-recursion arithmetic gives `2k=3d`. The converse evaluates `G` symbolically.

These facts refine Agent 4's `GModular.lean` and `Mod8Gateway.lean` and help identify mechanisms that could violate the **empirically observed**, currently unproved, odd-reset residue pattern.

## Exponentially sparse exceptional reset family

Suppose such a bad gateway occurs in a high-counter even excursion that started at reset `(2,N)`, following exactly `j` two-step high branches.

The preceding published high-branch recurrence gives
```text
a + 12 = 14 * 2^j,
a + c = N + 2*j + 2.
```
Combining these with `3*c=a+16` forces
```text
3*N + 6*j + 38 = 56 * 2^j.
```

`bad_gateway_reset_equation` proves this implication for all naturals. `bad_gateway_stage_even` proves from that equation **j must be even**, and `bad_gateway_reset_mod_eight` proves **(N+2*j) % 8 = 6**. For valid j, the exact exceptional reset size is therefore
```text
N_j = (56*2^j - 6*j - 38)/3,
j = 0,2,4,6,8,...,
N_j = 6,58,278,1170,4750,...
```
This list is an arithmetic necessary condition derived from the high-excursion model. The local proof establishes the equation, stage parity, and congruence for **any state satisfying the stated stage invariants**; it does not itself formalize the global proposition that every actual even excursion has those invariants. Their recurrence is elementary and already verified elsewhere in the repo.

**Important:** Such exceptional counter states genuinely exist for synthetic starts (e.g. reset `(2,58)`), and the argument does **not** prove that the actual blank-tape trajectory avoids them. The global exclusion of all `N_j` remains open. No claim of infinite nonhalting, a BB(6) bound improvement, or a resolved holdout follows.

## Why it is useful

Agent 1 observed that the few positive-even-c resets reached in a very long actual P1 prefix were all congruent to `2 mod 8`. Proving that residue pattern globally requires excluding rare paths through bad gateways, including the family above and certain small odd-phase states. The theorem supplies a precise structural target for that difficult reachability investigation. This narrows the questions an eventual inductive modular invariant must resolve.
