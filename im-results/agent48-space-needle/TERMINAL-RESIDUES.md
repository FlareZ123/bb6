# Space Needle terminal powers: universal mod-1000 one-step predecessor obstruction

**Agent 48; 2026-11-03.** Status: *locally Lean-kernel checked arithmetic theorem and source-shaped imported theorem, source-CI pending; intermediate negative-method result*. BB(6) remains unsolved. This result neither proves a blank-root halt nor nonhalt.

## Exact scope and source

Published `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371`, `BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean`, links original six-state blank tape to its exact high-level function starting from `N 1`. Original-source import and one-step inverse in this repository: [SpaceNeedleClosed.lean](SpaceNeedleClosed.lean), [SpaceNeedleRawBridge.lean](SpaceNeedleRawBridge.lean).

A positive power-of-two target with exponent K has counter `2^K-2`. Every nonterminal one-step source has uniquely `d+2=2^v*(2q+3)` for naturals q,v, with exact successor `d'=d+v+3(q+1)`. Hence a one-step predecessor of the target exists exactly when

```
2^(K+1)+3 = (2^(v+1)+3)*(2q+3) + 2v.
```

**Locally kernel-checked theorem `SpaceNeedleExp.thousand_predecessors`:** For every residue `r<1000` and every bound `B`, there exist naturals `K,q,v` with `K≥B`, `K mod 1000=r`, and the exact source equation above. No assertion is made that the source `d` is reachable on the real blank-start run. This is a rigorous obstruction to **eliminating an entire terminal-exponent congruence class modulo 1000 by proving every such target lacks all one-step predecessors**. It does not rule out refined source-reachability or residue-plus-state invariants.

### Exact constructive families

For all natural n:

- Even-source family: `K=12+18n`, `v=3`, `U=(2^(K+1)-3)/19`, `q=(U-3)/2`. The required congruences use `2^13 mod19=3` and `2^18 mod19=1`.
- Odd-source family: `K=3669+4098n`, `v=11`, `U=(2^(K+1)-19)/4099`, `q=(U-3)/2`. The required congruences use `2^3670 mod4099=19` and `2^4098 mod4099=1`.

All U are rigorously shown odd and ≥3, so the q formulas yield valid natural sources. The second family includes K=7767 (≡7 mod10) and K=11865 (≡5 mod10), falsifying the earlier candidate that these two infinite families have no one-step predecessors, based on finite K≤3000.

For a requested even residue r in [0,999], choose `n=((389*(r/2+494)) mod500)+500B`. Then `K=12+18n` has `K mod1000=r`. The key congruence is `9*389 mod500=1`. For an odd r, choose `n=((449*((r+331)/2)) mod500)+500B`; `K=3669+4098n` has `K mod1000=r`, since `2049*449 mod500=1`. Both `K≥B`. Every assertion is proved by exact arithmetic and finite modular identities.

## Evidence

- [TerminalResiduesArithmetic.lean](TerminalResiduesArithmetic.lean): first uniform mod-10 construction, theorem `selectK_correct`; local Lean 4.36.0-rc2 axiom audit `[propext, Quot.sound]`.
- [TerminalMod1000.lean](TerminalMod1000.lean): full kernel-checked generalized arithmetic, theorem `thousand_predecessors`; local Lean 4.36.0-rc2 axiom audit `[propext, Quot.sound]` with no `sorry`, `axiom` or local stub.
- [SpaceNeedleTerminalResidues.lean](SpaceNeedleTerminalResidues.lean) and [SpaceNeedleTerminalMod1000.lean](SpaceNeedleTerminalMod1000.lean): original-definition imports, and separate source-lemma integration, theorem `every_mod1000_has_predecessor`. A local surrogate compilation using signature-matching placeholders for **only two already proven original-source lemmas** succeeded, but that compilation's axiom list includes the placeholders. Original-source CI has not run successfully during the GitHub Actions incident; **do not claim source-CI certification** for this newly written bridge. The older source-imported `SpaceNeedleClosed.lean` has a successful earlier original-source run for its first seven theorems, while later appended lemmas require pinned success confirmation.
- Independent exact-integer reproduction `validate_terminal_mod1000.py`, run against every r=0..999 for B=0 and B=1, finds 2000 valid high-level transition witnesses, maximum K=4,097,571. SHA256 of CSV (B,r,K,v,bitlength(q)): `ed010bb6eb25c53394b1d2e500e190336c7e1490fea82ed8c535c88639a1f36a`.

## Significance, limitations and next test

The original blank-entry orbit can avoid an entire set of otherwise legal source states. No nonhalting root has been classified. Finite terminal exponent scans often show no predecessor, so no claim about density of predecessor-containing exponents. The theorem falsifies the tempting global statement `K≡5,7(mod10)` have no immediate predecessors and extends the method limitation to all modulus-1000 classes.

Before external novelty or publication claims: verify the imported bridge on an execution-capable source CI runner; compare to published predecessor arithmetic and check whether larger modulus families add an analytically useful constraint. To advance actual BB(6) closure, one must prove blank-reachability/avoidance of these predecessors rather than counting all-state inverse nodes. See pilot [research issue](../../research/issues/R-20261103T1434Z-agent48-needle-terminal.md).


## Stronger all-decimal-suffix theorem (Agent 48, 2026-11-03 15:06 UTC)

[TerminalDecimalAll.lean](TerminalDecimalAll.lean) locally kernel-proves the fully uniform theorem:

For **all** naturals a, r, B satisfying r < 10^a, there exist natural K,q,v with K≥B, K mod 10^a=r and
\[
2^{K+1}+3=(2^{v+1}+3)(2q+3)+2v.
\]
Moreover the proof directly establishes this for every r < 2·10^a modulo 2·10^a. No fixed decimal suffix, however long, can exclude **all** power-of-two terminal targets of that suffix by proving absence of all immediate incoming edges. This statement is about unrestricted predecessor states. It establishes neither blank-orbit reachability nor a Space Needle/BB(6) halt decision.

Constructive proof for m=10^a and y=floor(r/2), B arbitrary:

- Even r: let A=(10^a−1)/9, n=A(6+m−y)+mB, K=12+18n, v=3. Since 9A+1=m and K traverses the complete even residue classes modulo 2m, K mod2m=r. The prior symbolic theorem supplies the exact q.
- Odd r: let A=(2050^a−1)/2049, n=A(1834+m−y)+mB, K=3669+4098n, v=11. Since 2049A+1=2050^a=m·205^a, K mod2m=r. Again the prior symbolic theorem supplies q.

The kernel proof checks the geometric identities inductively and constructs both witnesses with exact modular arithmetic, without enumerating residues. The corollary for 10^a follows by reducing the stronger 2·10^a equality. Both \`SpaceNeedleExp.all_decimal_predecessors\` and \`SpaceNeedleExp.every_decimal_suffix\` have *local Lean 4.36.0-rc2 axiom audits exactly* \`[propext, Quot.sound]\`, with no sorry or user axiom. This extends and supersedes the fixed-modulus 1000 statement as an arithmetic method limitation.

[SpaceNeedleTerminalDecimal.lean](SpaceNeedleTerminalDecimal.lean) imports the previously published-source-associated \`SpaceNeedleClosed\` and carries this arithmetic result through \`highLevelNext_iff_oddTower\` and \`oddTower_factor\` to the actual high-level function. The proof typechecks locally with exact-signature source-lemma placeholders and its dependency audit consequently includes those placeholders; full imported-source CI has **not succeeded** because the shared runner fails before executing any steps. No source-certification claim until a successful original-dependency job.

[validate_terminal_decimal.py](validate_terminal_decimal.py) independently checks 4,551 deterministic witness parameters, exhaustively for powers 10^0 through 10^3 (three bounds per residue) and samples through 10^10, with exact modular exponentiation without astronomical tape or counter construction; parameters digest \`8963397546b9510ef067c8a455b78fdd240e9cd1f065440269b30c6b6b8f14ad\`. This cross-check is auxiliary to the all-a Lean proof.

This is a negative result for a narrow proposed proof strategy, not a claim of external novelty or a publishable root decision. Next work should seek a constraint on **real blank-origin** predecessors or a novel holdout decision.
