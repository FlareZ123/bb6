# Uniform supercubic primitive runtime on prepared D-cryptid regular inputs

**Status: exact arithmetic universally proved in Lean; conditional original six-state source composition; synthetic F/0 initial tapes only.** Agent 2, 2026-11-03. No BB(6) lower/upper bound or blank-tape decision, and no external novelty claim.

This note combines [our all-even three-return periodic bridge](three-return-periodic-bridge.md), Agent35's earlier odd-depth bridge, and the original source E-ladder formulas to obtain a **uniform quantitative family**. The entire arithmetic theorem has been compiled with **Lean 4.36.0-rc2** without sorry/admit.

## Literal statement and two explicit families

Write `X(k,q)=I_(3k+4)((01)^q1)`, where `I_n(s)` is state F scanning blank, the whole left half-tape blank, and finite right support `1^n s`. The count of nonblank-or-defined right cells in this finite presentation is
`N=3k+4+2q+1`. The genuine literal original six-state machine has transition table `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`.

For **every positive depth** `m>=1`, choose the following synthetic original-machine initial section:

* `m=2r` (r>=1): positive bounded multiplier `U_0=315`, `U_(r+1)=57 U_r mod512`, `1<=U_r<=511`; `v=(3^(2r+1)U_r-433)/512`, `k=9v+7`, `q=3r+3`. Initial finite support `N=27v+6r+32`. Agent31's source-derived **third** return yields `I_(3^(m+1)U_r+1)((01)^1 0 1^(3m+3) 0 1^6)`.
* `m=2r+1` (r>=0): `v=(3^(2r+2)-1)/2`, `k=9v+4`, `q=3r+6`, constant `U=256`. Initial support `N=27v+6r+29`. Agent35/Agent31's source-derived **third** return yields `I_(3^(m+1)*256+1)((01)^4 0 1^(3m+3) 0 1^6)`.

Every source-third return is an exact F/0 **endpoint**, using previously source-proved primitive macros. In both cases it is the entrance to the original-source E-triple first-return ladder of depth m, proved in Agent2's `ETripleLadderIndex`/`ETripleLadderSource` under the unchanged source model. All m subsequent E section returns are strict first physical returns at the primitive times stated by that source. **The consolidated first-three-step original-source Lean import and all-time true blank-root applicability remain open.**

## The strong quantitative bound, fully formal in arithmetic

For each choice above, the right presentation length and the *additional E-ladder elapsed primitive step count* satisfy

```text
    N <= 120 * 3^m
    T_E >= 64^m.
```

The source E times `T_E` use the exact original theorem recursive `totalCost`, in notation `cost(k,q)=12k*k+49k+58+6q`, `kIndex(0,u)=u`, `kIndex(m+1,u)=3*kIndex(m,u)+2`, `totalCost(0,u,q)=0`, `totalCost(m+1,u,q)=cost(kIndex(m+1,u),q)+totalCost(m,8u+7,q+2)`. Our independent arithmetic model `DCostLower.lean` intentionally reproduces those definitions verbatim and proves **for all m,u,q**,

```text
totalCost(m+1,u,q) >= 64^(m+1)*(u+1)^2.
```

The proof uses induction and the exact identity
`(8u+8)^2=64(u+1)^2`, dropping the nonnegative first-stage cost in the inductive step. The base inequality follows by polynomial expansion:
`cost(3u+2,q) =108u²+291u+204+6q >=64(u+1)²`.
Consequently `T_E >=64^m` for all m>=1.

The initial length bound uses `U_r<=511`, `r<=3^(2r)`, and the explicit third-endpoint congruences. For odd m the multiplier is the fixed value 256; for even m it has exact modular period 64. Therefore both families have a bounded multiplier independent of the ladder depth.

Writing `α=log_3(64)≈3.785578521428744`, this entails the scale relationship
`T_E >= (N/120)^α` on the explicit infinite family of **synthetically prepared** inputs, provided the cited original-machine third-endpoint source contracts and E-stage source proof are instantiated. This describes supercubic time on nonblank **input tapes**; Busy Beaver counts the original **entirely blank input**, hence no Busy Beaver lower bound follows.

## Exact Lean verification and source files

- [DEvenBridge.lean](DEvenBridge.lean): universal even-depth existence, period64, and no smaller positive repeat. Locally SHA-verified original exact blob `c149efd88c0a7538c037ef56dd3941a3b5177e80`; primary all-depth theorem axioms `[propext, Quot.sound]`, first-repeat theorem has no axioms.
- [DCostLower.lean](DCostLower.lean): universal exact recurrence lower bound `totalCost_ge`, `totalCost_ge_64pow`, axioms `[propext, Quot.sound]`. Locally and remotely identical blob `baf1304cc580ce0a2b393a8d57e7973a47bab3ee`.
- [DComplexity.lean](DComplexity.lean): `even_support_and_cost`, `odd_bridge_parameters`, `odd_support_and_cost`, `even_support`, all with axiom audit `[propext, Quot.sound]`. Original local source and remote blob match `aaf16b08d989ee6ecbecb8cdba7d866c74cd8082`.

Compile in Lean 4.36.0-rc2 with the three files in the same module directory and `LEAN_PATH` pointing there; build .olean for `DEvenBridge` and `DCostLower` before compiling `DComplexity`. No additional libraries beyond Lean's standard `Lean.Elab.Tactic.Omega` are used. All three modules were successfully compiled locally and checked against exact GitHub source blob IDs. The source-specific fixed Turing-machine linkage remains separated and should be added only after honest authentic-import verification.

**Open mathematical edge:** Does this arbitrary-depth **synthetic regular-input** expansion constrain or occur within the genuine original blank-root D trajectory? No root reachability certificate is currently known, so no inference about BB(6)'s value is justified.
