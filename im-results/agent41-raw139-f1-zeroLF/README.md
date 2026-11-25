# Raw139 F/1 sibling source certificates

Three exact F1 sibling cylinders of the raw139 partial table now have complete original-source Lean 4.36.0-rc2 audits. They share the first eleven transitions `[7,24,11,24,14,21,3,16,12,11,24]` and differ only in the F1 transition:

| F1 action | Exact parent table | Weighted bound | Terminal leaves | Original-source audit |
|---|---|---:|---:|---|
| 0LF | `[7,24,11,24,14,21,3,16,12,11,24,20]` | 1603 | 277 | [45604778890](https://github.com/FlareZ123/bb6/actions/runs/45604778890), artifact `15018045298` |
| 0RC | `[7,24,11,24,14,21,3,16,12,11,24,9]` | 3807 | 323 | [45607499262](https://github.com/FlareZ123/bb6/actions/runs/45607499262), artifact `15018441852` |
| 0RB | `[7,24,11,24,14,21,3,16,12,11,24,5]` | 290 | 461 | [45609382340](https://github.com/FlareZ123/bb6/actions/runs/45609382340), artifact `15018818460` |

Each accepted theorem bounds every compatible completion of its literal partial table. The three cylinders are pairwise disjoint because their F1 actions differ, but they cover only three F1 choices. They do **not** close the raw139 parent, prove the exact champion-score Cover, or change any global residual count by themselves. A count may be reduced only after a source-accepted consumer proves the exact parent inclusion, the certified children, and the explicit retained complement.

## Shared symbolic-gap mechanism

The symbolic zipper interpreter `Agent41SymSweep.lean` treats arbitrary finite tape segments as opaque gap variables and rejects any computation that tries to read into a gap. Its soundness theorem `run_sound` transports successful symbolic traces to every assignment of the unexamined segments. This supports quantified sweep recurrences rather than extrapolation from sampled executions.

The 0LF closure has 12 internal first-hole splits and 277 terminal leaves: 147 translated cycles, 72 last-hole queries, 45 FAR certificates, and 13 infinite-growth proofs. Its H9 suffix uses a recursively nested carry counter with six constructors; structural induction proves the core costs and the outer stage advances by two. See the individual 0LF dossier below.

## Individual sibling dossiers

- [0LF](ZeroLF.md): bound 1603; complete 277-leaf source certificate.
- [0RC](ZeroRC.md): bound 3807; complete 323-leaf source certificate, including four-phase nested carry, binary counter, and eight-period suffix mechanisms.
- [0RB](ZeroRB.md): bound 290; complete 461-leaf source certificate, including the H19 unary-drain and H20 binary-increment recurrences.

## 0LF details

The exact 0LF theorem is `BB6.Agent41F1ZeroLF.all_completions_weighted : ∀ m, compatible parent m → WeightedBound 1603 m`. Its parent table is `[7,24,11,24,14,21,3,16,12,11,24,20]`; the F1 action is 0LF, distinct from the sibling actions listed above.

The longest remaining last-hole query is at 1597 moves, leaving the standard six-step weighted allowance. The certificate uses the existing `FastThreeHoleAudit` with exact literal table matching.

Twelve exceptional cylinders admit exact affine-cost recurrence families. For H9 the suffix is instead a recursively nested carry counter:

- Counter constructors low, high, a(g), b(g), c(g), d(g).
- Next sends low→high→a(low), a(g)→b(g)→c(g)→d(g)→a(next(g)).
- The tape tail words are 011, 0111111, 000111·0·tail(g), 011111·0·tail(g), 0001111·tail(g), 0111111·tail(g), respectively.
- The core starts in C with left word 1·L, right tail(g), and reaches D with left L and right 0·tail(next(g)). Its exact costs are 37,33,9,25,9,24+coreCost(g), proved by structural induction.
- The outer D stage has left word 1 and right word 1111·(11)^n·110·tail(g); after 20n+93+coreCost(g) moves it reaches the stage (n+2,next(g)).
- The actual blank entry reaches stage(0,low) after 68 moves. Thus every compatible completion runs forever.

## Reproduction

- 0LF: `bash im-results/agent41-raw139-f1-zeroLF/reproduce.sh`; archive SHA-256 `15b951ad6c8c9b988e2a2f44a39671a938b4c2b0fbc264c72a4afe1a972b62bb`.
- 0RC: `bash im-results/agent41-raw139-f1-zeroLF/reproduce-zeroRC.sh`; archive SHA-256 `e714f0772d6e7df0d64e3da63153c8450e39abead67caf8fb5b61d1241e5dbd8`.
- 0RB: `bash im-results/agent41-raw139-f1-zeroLF/reproduce-zeroRB.sh`; archive SHA-256 `dedb53f31b5493b240d1b1d89fa1c409f0ced92ef1d6486c5415e6d98fe75aba`.

The manual workflow `agent41-raw139-f1-zeroLF.yml` accepts the sibling selector and pins the exact source revision. All three source audits are independent of the still-missing raw139/global roster consumer. Do not promote the sibling count to a global result without that consumer.


## Draft 0RB roster consumer

`ChampionF1ZeroRBIntegration.lean` is an uncompiled draft. It imports the existing canonical77/0RC chain and accepted 0RB certificate, checks the exact depth-five child `championChild 5 ⟨false,true,1⟩`, and removes only that parent from the 106-leaf F1 residual list. Proposed counts are 105 retained raw139 leaves and 181 total obligations (76 non-champion canonical entries + 105 raw139 leaves). The draft preserves the complement and exposes conditional exactness. These counts are not accepted until the existing manual source workflow compiles the complete closure and named axiom profiles.
