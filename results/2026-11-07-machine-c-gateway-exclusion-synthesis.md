# Machine C: source-certified residual gateway exclusions

**Status: a substantial necessary-gateway reduction, not a Machine C nonhalting proof.** The exact six-state, two-symbol Busy Beaver value remains unknown.

This synthesis concerns the published Machine C

`1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`

and its exact blank-entry accelerated orbit. The source-level bridge from the original Turing machine to the counter acceleration is independently verified in [Agent 21 CI 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481).

## 1. Reset gateway

Write (n) for the reset index in the necessary gateway state

`Reach (2*n+1, 3*n+4, 0)`.

The current combined filter excludes at least **1409 of the 2048 residue classes**:

- The Agent 41 modulus-1024 finite quotient excludes 678/1024 reset residues. Its lift covers 1356/2048.
- The source-certified theorem for (n\equiv38,130,184,271\pmod{512}) adds five previously surviving modulus-1024 residues:
  `38, 130, 184, 642, 783`.
  These lift to ten additional modulus-2048 residues. The four infinite families are proved for every natural parameter by [the four-family source certificate](2026-11-02-machine-c-four-new-mod512-gateway-exclusions.md), independently compiled in [CI 41410929224](https://github.com/FlareZ123/bb6/actions/runs/41410929224).
- The source-certified modulus-2048 theorem adds 43 further residue classes, disjoint from both preceding filters:
  `42,128,166,183,267,394,411,439,474,498,535,546,582,654,747,792,824,911,952,978,1003,1056,1070,1099,1119,1160,1239,1248,1322,1344,1416,1458,1472,1498,1504,1646,1766,1778,1862,1871,1896,1954,1994`.
  Each class is excluded for every natural parameter by its own Lean theorem in [the 43-family result](2026-11-02-machine-c-forty-three-new-reset-mod2048.md), compiled in [CI 41414685974](https://github.com/FlareZ123/bb6/actions/runs/41414685974).

Thus the reset-gateway exclusion count is at least

[
1356+10+43=1409
]

out of 2048 residue classes. The other 639 classes are outside this combined filter; that does not imply that any of them is reachable.

## 2. Side gateway

Write (n) for the index in the side gateway state

`Reach (0, 4*n, 24*n+23)`.

The Agent 41 modulus-1024 quotient excludes 540/1024 side-index residues. The source-level theorem proves 42 infinite families modulo 512. After intersecting with the later quotient, ten families remain genuinely new:

`n ≡ 34, 66, 151, 290, 427, 428, 436, 478, 484, 492 (mod 512)`.

Each contributes its two lifts modulo 1024, namely (r) and (r+512), giving twenty new residues. The combined side-gateway filter therefore excludes at least

[
540+20=560
]

of 1024 side-index residues. The complete all-natural source proof, including all 42 original families and the exact later-quotient intersection, is in [the 42-family side result](2026-11-02-machine-c-forty-two-new-side-gateway-exclusions.md), independently compiled in [CI 41414454382](https://github.com/FlareZ123/bb6/actions/runs/41414454382).

## 3. Evidence boundary

The three component results are all-time source-level exclusions: their Lean theorems quantify over every natural family parameter and prove that the corresponding gateway state is never reached. The generator used for some inverse trees has no logical authority. The original-machine/counter-acceleration correspondence is separately source-checked.

The quotient baselines have a different status. Their finite closures were computed by independent traversals and accompanied by Lean proofs of abstract-transition soundness; the numerical closure counts themselves are computational certificates, not kernel-proved cardinality theorems. The source-family additions are directly kernel-checked and must remain distinguished from that quotient evidence.

The resulting counts are necessary-gateway coverage figures. They do not imply global Machine C nonhalting, decide the remaining gateway residues, or determine BB(6).

## 4. Prior art and scope

Google DeepMind's [Cryptids formalization of the corresponding Machine C](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC/) already formalizes the underlying acceleration. The acceleration itself is therefore prior art. The contribution recorded here is the additional all-time nonreachability of the explicit infinite gateway families. The targeted external review did not establish global priority for those individual residue families; stronger novelty claims require a fuller literature comparison.

The nine earlier Machine C notes that were quotient-known or specializations of broader source theorems remain preserved under [the publication qualification archive](../im-results/machine-c-publication-audit/README.md). Their proofs and provenance have not been discarded.

## 5. Remaining mathematical obligation

The remaining reset and side residues still form infinite search spaces. A complete result requires either a global authentic blank-root nonhalting invariant for Machine C or an exact halting witness, followed by the wider six-state maximality argument needed to determine BB(6). None of the gateway counts above supplies that missing step.
