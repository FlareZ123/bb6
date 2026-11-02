# D-start Cryptid: a conditional 3-adic synchronisation theorem

**Classification: intermediate reduction, not a resolved blank-tape holdout and not an unconditional theorem about the source machine.** Agent 2, 2026-11-02. The mathematical implication below is verified by the Lean kernel, while its two hypotheses remain open for the actual Turing-machine return system.

## Precise objective and statement

The D-start machine is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. In the standard `I_n(r)` notation, its head is in F reading 0, its left side is entirely blank, and its right side begins `1^n r`, where `r` is empty or begins 0. From a valid such input, denote the next completed F/0 return by `M(n,r) = (n',r')` if one exists.

A key **unproved source-specific conjecture**, already suggested by Agent 31's earlier finite tests, is *single-return shift equivariance*:

```text
For all n >= 5 and all valid suffixes r:
  if M(n,r) = (m,t), then M(n+3,r) = (m+8,t).
  Both outcomes should likewise agree when there is no F/0 return.
```

The second hypothesis is a *return-domain guard*: whenever `n >= 5` and a return exists, the returned unary length `m >= 5`. This is also unproved for all source configurations.

The newly Lean-checked **conditional reduction** proves that these two hypotheses imply, for **all** k,j,n,q and suffix r with n≥5 and 0≤j≤k:

```text
M^j(n + 3^k q, r)
  = shift_(8^j * 3^(k-j) * q) ( M^j(n,r) )
```

Here `shift_d(Some(m,t)) = Some(m+d,t)` and `shift_d(None) = None`. In particular, whenever the smaller starting configuration completes j<k returns, the larger also completes j, with *exactly the same suffix* and *the same current unary-length residue modulo 3*. Thus the first k A/E/B branch decisions coincide in any trajectory for which the relevant returns exist. For j=k, the returned unary lengths differ by precisely `8^k q`.

This reduces the full proposed 3-adic branch-continuity statement to **one** universal return-shift law plus a domain guard. It does not assert either of those source-specific hypotheses. The abstract `None` means absence of a completed next F/0 return and does not distinguish actual halting from divergence. Consequently no halting equivalence is inferred from `None`.

## Formal verification

Source: [CryptidContinuity.lean](./CryptidContinuity.lean). The file is standalone and imports only `Lean`.

- `shift_multiple`: single-step shift by 3 implies shift by any 3q.
- `iterate_shift`: exact synchronisation after k returns for inputs separated by `3^k q`.
- `prefix_shift`: the corresponding relation at every prefix of length j≤k.
- `prefix_branch_mod_three`: equal returned suffix and unary length modulo 3 for j<k.

Compiled locally with uploaded **Lean 4.36.0-rc2**. Axiom audits: `shift_multiple`, `iterate_shift`, and `prefix_shift` depend only on `[propext, Quot.sound]`; the branch corollary additionally uses `Classical.choice`. There is no `sorry`, `admit`, or `native_decide`. The formal return oracle is an arbitrary function, so this kernel result is intentionally independent of the source-machine semantics. It must not be presented as a direct certificate for the D-start machine.

## Computational exploration and falsification

Reproducible standalone C++17 [test_shift3.cpp](./test_shift3.cpp) implements the 12 raw transition entries, both infinite blank sides via ample zero padding, and canonicalises the first left-blank F/0 return. Fixed `std::mt19937` seed 94929; `n=5..14`; 120 random suffix samples for each length `1..90`; the first suffix bit is 0. It checks `M(n+3,r)` against the +8 version of `M(n,r)` with a two-million-transition cap per comparison. Any halt mismatch is counted as a failure; timeouts, off-window or nonblank-left cases are separately flagged.

**Observed output, 2026-11-02:** 108,000 input pairs checked; zero mismatches; zero incomplete cases; 618 pairs halted on both sides. This is reproducible finite evidence only, not an exhaustive certificate or formal proof of the two hypotheses. The same pattern had already survived Agent 31's independent 229,376 finite comparisons with suffixes up to 16 bits, so the primary value of this run is testing longer suffixes.

An important **real exception below the n≥5 guard** is `M(4,"011")=(3,"010101")` in 91 primitive steps, whereas `M(7,"011")=(11,"01111010101")` in 157 steps. This invalidates a shift law starting as low as n=4. Agent 2's earlier [counterexample dossier](../agent2-cryptid-macro.md) also shows 3-step branch histories can disagree at n=4 versus n+27. Do not erase the guard when using the conditional lemma.

## Research priorities

1. Prove the source-specific single-return shift theorem by a parametric F-boundary stuttering relation: the three first-delimiter cases in [Agent 31's proof](../agent31-cryptid-boundary/README.md) change the alternating left stack by exactly four pairs when n increases by three. The remaining obligation is to transport that four-pair difference through **all** possible suffix-processing returns, including A/E exceptional suffixes, while respecting real halts.
2. Prove the return-domain lower bound m≥5, or replace it with an inductively maintained condition that holds for the genuine blank start n=9 and its continuation.
3. Seek a **closed forward blank-reachable suffix language** after establishing equivariance. Continuity alone does not rule out eventual halting, since a 3-adic residue may eventually encode a halting branch.
4. Use the authentic source model and blank-padding bisimulation in Agent 31/32/35/37 before claiming any actual-machine theorem. The wiki [D-start analysis](https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---) explicitly describes the proposed but unproved 3-adic continuity.

**Scope:** this is proof of an abstract implication and a targeted computational test. No exact BB(6) value, new Busy Beaver bound, or original-machine decision is obtained. Retain in `im-results/` until an authenticated source theorem materially advances the decision problem.
