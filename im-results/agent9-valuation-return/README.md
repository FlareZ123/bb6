# Cryptid S-section: exact maximal zero-burst return and its limitation

**Status: intermediate source-derived arithmetic, not a six-state root decision.**
Programme: [seeded valuation-return pilot](../../research/issues/R-20261103T0753Z-agent9-s-valuation-return.md).
Machine RLE: `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`.
Primary high-level source: [Google DeepMind Cryptids S/T acceleration](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean).
The standalone `Sstep` definition is the arithmetic `q=b+16` conjugate of the published S branch; it has **not** been imported from the unchanged upstream Lean source into this proof. For genuine S states `q>=16`. **`none` in this S-only proof means S-to-T section transfer, never the source Turing machine halting.**

## Exact return statement

Write `q=3a+r`, `r∈{0,1,2}`. The S counter step from `(q,c)` is:

- `r=0,c>0`: `(4a,c-1)`; `r=0,c=0`: transfer to T;
- `r=1`: `(4a-3,c+4)`;
- `r=2`: `(4a+1,c+6)`.

For a nonzero-residue input `q`, let `q1` be its next counter and let `δ=4` or `6` be its height increment. Write `q1=3^v u` with `u%3≠0`, i.e. `v=v3(q1)`. The entire *first maximal zero burst* is decided by one comparison:

- If `v<=c+δ`, exactly `1+v` S steps reach the next nonzero-residue counter `(4^v u,c+δ-v)`.
- If `v>c+δ`, the first `c+δ` zero steps consume the remaining height; the next S step transfers to T. Including the initial nonzero step, the transfer occurs after `c+δ+2` S steps.

The second case is a source-model **S→T transfer** only. Its eventual raw-TM halting consequences require analysis of subsequent T states.

## Lean checked statements

[ValuationReturn.lean.gz.b64](ValuationReturn.lean.gz.b64) restores to a 6,652-byte source (`SHA256 c6eb9f6b9b7f5124a156b14c3fac299c97c38edd150fbcffe1f1a22e0a090d77`). Lean 4.36.0-rc2, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`, locally compiled it with no `sorry`. Its theorem names and exact boundaries:

- `zero_prefix`: for `k<=n` and `k<=height`, precisely `k` zero-branch steps send `(3^n*u,height)` to `(4^k*3^(n-k)*u,height-k)`.
- `zero_transfer_if_valuation_exceeds_height`: for `height<n`, `height+1` steps from `(3^n*u,height)` transfer to T.
- `nonzero_core_burst` and `nonzero_core_is_maximal`: one nonzero branch followed by a quantified zero burst, with the resulting counter coprime to 3 if `u%3≠0`.
- `nonzero_then_transfer`: an exact sufficient divisibility condition for the opposite outcome.
- `adversarial_all_heights`: for all natural `c`, define `a(0)=0`, `a(n+1)=9*a(n)+2`. Then `steps (c+6) (some (3*a(c+5)+4,c))=none`: an explicit **synthetic** input that transfers at every height. [ValuationValidity.lean](ValuationValidity.lean) additionally proves that each such counter is at least 16 and congruent to 1 mod 3.

Axiom audits for all headline theorems list only `[propext, Quot.sound]`; no `sorryAx`, custom axiom or unverified external theorem is used in these standalone statements. These extend existing **fixed-length** zero-burst lemmas in [Agent9's earlier work](../agent9-s-section/README.md) to a compositional nonzero-core certificate. The simple adversarial family demonstrates why arbitrary nonzero residues and an initially positive height do not give universal survival. The source contains no proof that either genuine rooted input satisfies the required all-time valuation inequality.

## Constructive exact first-transfer compiler

The additional kernel-checked [Split3.lean](./Split3.lean) supplies a terminating executable `split3(n)=(v,u)` with a complete positive-input factorization proof `3^v*u=n` and `u%3≠0`. For every `q>=16`, `q%3≠0`, set `(v,u)=split3(onNZ q)`. The theorems `nonzero_core_exact` and `nonzero_core_transfer_exact` discharge the earlier explicit decomposition hypothesis, giving the **unconditional parametric dichotomy** in the first section. `nonzero_core_first_transfer` also proves no transfer occurs on any earlier S step, thus certifying the *first* S→T transfer time. Local Lean 4.36.0-rc2 compiled all with axiom audits `[propext, Quot.sound]`, no sorry. These are reusable source-derived arithmetic results, not source-imported Cryptids raw Turing machine theorems. They repackage the existing zero-burst mechanism constructively, rather than resolve either fixed root.

## Independent finite checking

[burst_verify.py.gz.b64](burst_verify.py.gz.b64), restored Python SHA256 `014a416ca576dfa87757bbb6aa407067daad557cdf92ac89daf433e8c2f84ad6`, compares every maximal-burst macro to independently iterated direct S steps. The target entries `(141,3)` and `(17,3)` are respectively the published root and a separately authenticated S-root; they are distinct original-machine roots. Exact local 100,000 S-step checks per entry:

| Root q | Steps | Macro returns | Minimum checked c-v3(q) at macro start | Longest zero burst | End c | End q bitlength |
|---|---:|---:|---:|---:|---:|---:|
| 141 | 100,000 | 66,660 | 2 | 11 | 299,654 | 41,511 |
| 17 | 100,000 | 66,739 | 3 | 12 | 300,232 | 41,508 |

No transfer occurred in either finite run. These checks certify **only finite prefixes**. They are not a nonhalting argument. Hashes of resulting counter big-endian bytes are respectively `40b3000ec85ad750867546a4cbe54854c5ccd2fc9e9f37ec58e646b3d82550bc` and `9f322dbc76be556524d9593d59adb7a502d7eecd277651df8a6630f61cf1908b`.

## Reproduce and limitations

From this directory run `python reconstruct.py` (requires Python's `filelock` package); it validates source SHA256 and writes source atomically under locks. Set the local Lean module search path to the directory, compile `ValuationReturn.lean` to an `.olean`, then compile `ValuationValidity.lean`; run `python burst_verify.py` for the exact finite cross-check. The two primary compressed files preserve portable proof source and verifier source with an idempotent reconstruct helper. Do not replace the published Cryptids machine semantics with this standalone map when making a root claim.

**Assessment:** mathematically checked source-derived return structure and a genuine method-limitation family, but the fixed-root all-time valuation inequality remains unresolved. External novelty relative to standard Collatz accelerations is unestablished; nothing is promoted to `results/`. Future productive work would need a seed-specific history-sensitive obstruction against `v3(q1)>c+δ`, preferably imported into the original Cryptids proof chain. Longer traces alone are unlikely to change the root decision.
