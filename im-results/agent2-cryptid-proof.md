# Agent 2: Lean-verified exact halting-time theorem for synthetic cryptid tapes

**Classification:** Reproducible auxiliary mathematical result about specially prepared tapes. It does **not** resolve any BB(6) blank-tape holdout, change known bounds, or establish the exact BB(6). Preserved under `im-results/` pending assessment of novelty and frontier relevance. Verified against Lean **4.36.0-rc2** on 2026-11-02.

## Machine and configuration

A standard two-symbol machine with 6 states A through F:
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. An entry `1RB` means write 1, move right, enter B. `---` is a halting transition, here from F reading 1. This is the D-start representative of an existing BB(6) cryptid.

Let `S(k)` for `k >= 1` be the infinite blank tape with a finite block `0 1^(3k+1) 0 1 1 0 1 1`, head on the initial 0, and state F. Then **the first halt is exactly at**

`T(k) = 12*k*k + 17*k + 69`.

The theorem is about this entire infinite family, not only a finite enumerated sample.

## Formal statement

The complete self-contained Lean proof is stored in compressed reversible form:

- `im-results/agent2-cryptid-proof.lean.xz.b64` (xz-compressed and then base64-encoded UTF-8 Lean source)
- `im-results/agent2-unpack-proof.py` (reconstructs file atomically with file lock; requires Python `filelock`)
- Expected source SHA-256: `58e4beca8f67073460c098d43a7043a93c7a708c1d32aceff299d8bf98e3489d`
- Reconstructed source: `im-results/agent2-cryptid-proof.lean`

After restoring the source, run it with Lean 4.36.0-rc2. The audit prints:
```
'CryptidPhase.synthetic_family_halts' depends on axioms: [propext, Quot.sound]
'CryptidPhase.synthetic_family_last_step' depends on axioms: [propext, Quot.sound]
'CryptidPhase.synthetic_family_first_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
```
There are no `sorry` or `native_decide` escapes in this proof.

The key Lean theorems are:
1. `macro_C`: exact `6*(m+1)+27`-step transition from `C(m+1,r+1)` to `C(m+5,r)` for all natural `m,r`. These are arithmetically nontrivial symbolic tape identities.
2. `start19`: the prescribed family enters `C(3,r)` in exactly 19 primitive steps.
3. `phase2_halts` and `phase2_notyet`: closing suffix needs exactly `2*(m+1)+73` steps for `C(m+1,0)`.
4. `synthetic_family_halts`: halting at the closed-form time `T(r+1)`.
5. `synthetic_family_first_halt`: every earlier time `t < T(r+1)` has nonhalting configuration.

The Turing-machine state/tape transition function is explicitly defined with both unbounded sides represented by lists, extended by zeros. The halting configuration is frozen, and the proof checks that it was nonhalting at time `T-1`.

## Proof skeleton

Start at F reading the zero before a unary run of length `3(r+1)+1`. In 19 transitions reach `C(3,r)`. For each unit removed from the triple-one counter, perform one macro transition consuming `6m+27` steps and increasing `m` by 4. Once the counter is exhausted, the closing tape takes `2m+73` steps. The exact total is
`19 + sum_(j=0)^(r-1) (6*(3+4*j)+27) + 2*(3+4*r)+73 = 12*(r+1)^2+17*(r+1)+69`.
Every recurrence is proved as actual finite transitions in Lean, with no inductive hypothesis about undocumented macro behaviour.

## Scope and next actions

The family starts from specially programmed tape content and so proves no relation to the blank-tape orbit. The macro method can inform future search for inductive certificates for genuine BB(6) holdouts. The existing source `https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---` includes closely related macro discussions; compare before claiming novelty. A valuable next step is finding a reachable blank-tape prefix that enters a similarly tractable macro section, or a credible nonhalting invariant for the actual blank tape.
