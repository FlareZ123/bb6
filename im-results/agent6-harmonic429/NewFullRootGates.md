# Seven complete terminal cylinders in the genuine #429 blank orbit (2026-11-04)

Agent 6, research intermediate. The six-state Busy Beaver function and original machine #429 remain unsolved. No proposed exact BB(6) value or upper bound follows.

## Exact statements and proof status

For every natural accelerated time `n` and counters `a,b`, the authentic blank-root local map satisfies the following hypotheses:
```lean
BB429.run n (0,0) = some (a,b)
b + 1 = 2*a
```
Its terminal first counter `a` cannot lie in the following **full unbounded families**:

| residue | Lean theorem | CI status |
| --- | --- | --- |
| 329 modulo 512 | `BB429No329.blank_halt_not_329_mod512` | Original repository modules [41936215566](https://github.com/FlareZ123/bb6/actions/runs/41936215566), success |
| 309 modulo 512 | `BB429NewSix.blank_halt_not_309_mod512` | [41936565123](https://github.com/FlareZ123/bb6/actions/runs/41936565123), success |
| 373 modulo 512 | `BB429NewSix.blank_halt_not_373_mod512` | Same, success |
| 457 modulo 512 | `BB429NewSix.blank_halt_not_457_mod512` | Same, success |
| 501 modulo 512 | `BB429NewSix.blank_halt_not_501_mod512` | Same, success |
| 181 modulo 1024 | `BB429NewSix.blank_halt_not_181_mod1024` | Same, success |
| 81 modulo 512 | `BB429No81.blank_halt_not_81_mod512` | [41937192793](https://github.com/FlareZ123/bb6/actions/runs/41937192793), pending at 23:54 UTC; DO NOT count as source certified until success |

The first six statements have **unchanged-repository accelerated-source** Lean 4.36.0-rc2 checks; the seventh source verification is pending. None of these new files has yet been audited against the **upstream original Cryptids raw-TM source**, which is a separate provenance obligation. The local proof facades used only during exploratory compilation are not the published source; successful CI imports the exact original `BB429Rank.next/run`, `BB429Mod8.Allowed`, Agent6's inverse lemmas, and Agent39's stronger root invariants.

## Reproduction

- The first result is plain source [`BB429No329mod512.lean`](BB429No329mod512.lean).
- Five further theorems are in compressed, immutable [`BB429NewSix.lean.xz.b64`](BB429NewSix.lean.xz.b64), SHA256 of reconstructed source `00ec61dedf471df1fe44151d65e5b2bca6bf1d6593e4344ce5eec194856ac460`. [Unpacker](unpack_new_six.py) uses a lock, atomic replacement and SHA256 verification.
- The exceptional-rank certificate is compressed [`BB429No81mod512.lean.xz.b64`](BB429No81mod512.lean.xz.b64), source SHA256 `6136100818994f4f645968baaa4cb511498bc838b665daf8fae064d793973cd4`; [unpacker](unpack_no81.py).
- The single [manual-only proof workflow](../../.github/workflows/agent6-429-new-gates.yml) runs the corresponding original-module checks; no per-commit triggers.

## Mathematical mechanism

The unique machine halting condition is `b+1=2*a`; genuine accelerated seed is `(0,0)`. The published Agent6 exact `odd_back` and `even_back` prove every possible predecessor in the invertible branches. These new proofs backchain affine families `(M*q+r,2*(M*q+r)-1)`, keeping `q : Nat` universally quantified, and force either an unreachable `BB429Mod8.Allowed` residue or an impossibility from Agent39's source-established rooted invariants:

- A genuinely reached **positive even** first counter implies second counter `%8=2`.
- A reached first counter `%16=1` implies second counter `%8≠6`.
- A reached first counter `%32=5` implies second counter `%16≠1`.

For `a%512=81`, the final backchain reaches `(80*q+9,1888*q+282)`. Every `q>0` forces a positive-even ancestor `(20*q,2008*q+294)`, whose second counter is 6 modulo8; the alternative predecessor violates `Allowed`. At `q=0`, the exceptional target is `(9,282)` with rank `2*9+282=300`. The actual blank sequence has `run 50 (0,0)=some(109,66)` (rank284) and `run 51 (0,0)=some(11,282)` (rank304). `BB429.run_rank_bounds` establishes strictly monotone rank across successful transitions and excludes the exceptional state at any time, for any trace length. The new source verifies both checkpoints with `by decide` rather than trusting printed Python data.

## Novelty and limits

Agent30's previously source-verified `38/1024` necessary-root gate has candidate residue set
```text
9 53 73 81 117 181 201 209 245 309 329 337 373 437 457 465
501 565 585 593 629 637 649 693 713 721 757 765 821 841
849 885 893 949 969 977 1013 1021
```
Under that **source predicate**, the first six new statements remove eleven pairwise-distinct residue classes modulo1024 (`309/821,329/841,373/885,457/969,501/1013,181`), leaving 27 candidate classes. The seventh `81(mod512)` would remove another two (`81/593`) to give 25 necessary classes **upon original-source verification**. This is arithmetic composition of proved necessary restrictions, not a separately kernel-checked single combined `IsHalt` iff. Agent1's two 2048 and Agent6's four 8192 and Agent39's six 16384 additional exclusions are outside this simple 1024 tally; compare exact overlaps when composing.

These are genuine unbounded parameter exclusions, but do not close all gateways for one machine and cannot establish a BB(6) bound. The direct inverse-tree technique may overlap existing generalized classification methods. A complete original-source raw bridge and external novelty review remain open. Next valuable research should target an entire surviving sector across all 2-adic lifts, or a uniform blank-root nonhalting obstruction, rather than multiplying residue counts without a decision mechanism.
