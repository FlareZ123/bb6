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

The second hypothesis is a *return-domain guard*: whenever `n >= 5` and a return exists, the returned unary length `m >= 5`. This is also unproved for all source configurations. The threshold 5 was used as a deliberately conservative proof parameter before the false n=4 return marker was diagnosed; it should not be interpreted as a demonstrated sharp boundary.

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

**Observed output, 2026-11-02:** Original first run checked 108,000 pairs with n=5..14 and no mismatch. **Revised physically correct test** checks 140,400 random pairs n=2..14 with the same seed, suffix lengths 1..90, and no mismatches or incomplete cases; 851 pairs halt on both sides. The revised program maintains an exact count of 1s strictly to the head's left and only accepts F/0 when the count is zero. It continues through interior F/0 passes that have nonblank left tape. This is reproducible finite evidence only, not an exhaustive certificate or formal proof of the two hypotheses. The same pattern had already survived Agent 31's independent 229,376 finite comparisons with suffixes up to 16 bits, so the primary value of this run is testing longer suffixes.

**Correction of an earlier false counterexample:** the old Agent 2 script treated a state-F/0 pass with nonblank left tape as a legitimate first return. Its purported 91-step `I_4(011)` successor actually has left list `1011`; the genuine first return is at **96** steps, to `I_3(01111010101)`. The matching `I_7(011)` return takes **157** steps and yields `I_11(01111010101)`. The previously alleged 3-step mismatch for n=4 versus n=31 vanishes; both branch strings are `E,A,A`. The complete finite no-earlier-return certificates for n=4 and n=7 are in [ReturnGuard.lean](./ReturnGuard.lean), compiled against the checksum-restored original machine in [CI 41442257562](https://github.com/FlareZ123/bb6/actions/runs/41442257562). All returned theorem axiom reports are empty. The existing abstract theorem retains its **arbitrary n≥5 guard as a formal hypothesis**; it does not prove n=4 is exceptional. Source-specific n↦n+3 equivariance may hold already for n≥2, but this remains conjectural.

## Research priorities

1. Prove the source-specific single-return shift theorem by a parametric F-boundary stuttering relation: the three first-delimiter cases in [Agent 31's proof](../agent31-cryptid-boundary/README.md) change the alternating left stack by exactly four pairs when n increases by three. The remaining obligation is to transport that four-pair difference through **all** possible suffix-processing returns, including A/E exceptional suffixes, while respecting real halts.
2. Prove the return-domain lower bound m≥5, or replace it with an inductively maintained condition that holds for the genuine blank start n=9 and its continuation.
3. Seek a **closed forward blank-reachable suffix language** after establishing equivariance. Continuity alone does not rule out eventual halting, since a 3-adic residue may eventually encode a halting branch.
4. Use the authentic source model and blank-padding bisimulation in Agent 31/32/35/37 before claiming any actual-machine theorem. The wiki [D-start analysis](https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---) explicitly describes the proposed but unproved 3-adic continuity.

**Scope:** this is proof of an abstract implication and a targeted computational test. No exact BB(6) value, new Busy Beaver bound, or original-machine decision is obtained. Retain in `im-results/` until an authenticated source theorem materially advances the decision problem.


## Additional authentic-source E branch proofs (2026-11-02)

[**EOneZeroHalt.lean**](./EOneZeroHalt.lean) proves a new universally quantified guarded halting cylinder of the D-start original six-state machine: for every k≥0 and arbitrary finite binary suffix ys, starting at F/0 on `1^(3k+4) 0 101101100 0 ys` enters frozen halt state 6 for the **first** time at `12k²+41k+147` primitive transitions. The additional zero after 101101100 is essential: with suffix `111` and no zero, the machine returns instead of halting. The proof expands 114 exact E-boundary steps into fixed symbolic chunks and composes with Agent31's original-source `prefix_E`. [Successful SHA-verified original-source Lean CI 41441110080](https://github.com/FlareZ123/bb6/actions/runs/41441110080), audit only `[propext, Quot.sound]`, no unproved placeholders.

[**ReturnGuard.lean**](./ReturnGuard.lean) imports that same original raw model and corrects the earlier false 91-step marker with completely axiom-free finite kernel evaluations, proving no physically blank-left F/0 return at any time 1..95 for the n4 case or 1..156 for n7. Both exact return configurations are source-proved. [Successful CI 41442257562](https://github.com/FlareZ123/bb6/actions/runs/41442257562).

[**EOneTripleReturn.lean**](./EOneTripleReturn.lean) extends the complementary E boundary `0 101101100111 ys` and gives a conjecturally universal exact return:
`I_(3k+4)(0 101101100111 ys) -> I_(8k+3)(01111010101010101010 ys)` after `12k²+49k+170` raw transitions. The 134-step E-to-B bridge was locally Lean-verified in a standalone raw machine model; authentic original-source CI is pending. This is a conditional tape family and does not imply blank-orbit behavior.

These branch certificates remain **intermediate** and should not be promoted to `results/` without a demonstrated advance toward original blank-machine closure.
