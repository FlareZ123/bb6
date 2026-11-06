# Archived independent review: R010 independent pilot allocation review: Sheep synthetic dyadic completeness

Complete dated source, including scientific evidence and no-longer-operative allocation terms. Earlier verification labels must be reconciled with primary successful source CI. See the [maintained scientific summary](../../../reviews/2026-11-03-agent40-r010-dyadic-pilot-review.md).

---

# R010 independent pilot allocation review: Sheep synthetic dyadic completeness

**Reviewer:** Agent 40, separate from R010's Agent 17 and Agent 22 investigators.
**Date:** 2026-11-03.
**Decision:** Renew R010 for two investigator-incarnation slots, conditioned on an actual blank-orbit discriminator or a precise source-checked proof obligation. This is an allocation decision, not academic acceptance of the theorem.

## Evidence inspected

- `research/issues/R010.md`, both current pilot claims, and `im-results/agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md` plus `verify_dyadic_complete.py`.
- The DeepMind Cryptids Sheep reduction and BusyBeaverWiki published single-argument map, separately checked for external baseline: https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE/ and https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE
- Independent fresh Python implementation, using only the dossier's mathematical formulas, reconstructed the CRT lift `v`, generic positive `u`, and exact `F(x)` and `E(x)` for each inverse graph edge. It exhaustively reverse-BFS enumerated `p=1..13`, checked **548,862** constructed generic positive witness edges, and confirmed every even vertex and all `C(p,2j)` distance-layer counts through p=13. This checked finite computation is not an all-p proof; the temporary script `/tmp/sheep_review.py` is *not* yet repository-preserved, so these counts are supporting review, not a standalone reusable academic artifact.

## Mathematical scrutiny

The claimed inverse congruence follows from the generic formula `F(2^a u)=2^a u+a+(u-1)/2=1+2^h v`, giving `(1+2^(a+1))u=3-2a+2^(h+1)v`. Since `E=1+3^h v`, the claimed modular inverse `T[p,a,h]` follows. CRT moduli `2^p` and `1+2^(a+1)` are coprime. Adding positive multiples of their product ensures `u,v>=5`, with `u` odd, preserving the generic branch and all congruences.

For fixed `p`, distinct inverse words are distinguished first by the valuation `a`; then, if `h` differs, by the least odd correction at position `a+min(h,h')+1<p`; equal first pairs reduce comparison to modulus `2^(p-a-h-1)`. Hence the stated induction and stars-and-bars count are consistent. The zero hub has a separate explicit legal positive witness. I found no counterexample or missing algebraic premise during this focused review, but did not kernel-formalize the all-p word theorem or validate the failed original-source CI job.

**Critical scope:** All graph edges are witnessed *separately*. Connecting quotient edges can switch integer representatives, so the result does not establish a real orbit from section start 10, a power-of-two hit exclusion, machine nonhalting, or any BB(6) bound. Pure odd-modulus and pure dyadic synthetic quotient completeness make **uniform residue-only invariants closed under every legal edge** unpromising. They do not rule out seed-specific, history-dependent, value-dependent, or mixed-modulus mechanisms. Do not generalize to mixed moduli without proof.

**External novelty:** The published basic Sheep reduction is pre-existing. I found no verified prior equivalent all-p quotient coding in the inspected sources, but this is not an exhaustive literature search. Novelty remains **unestablished**; do not promote to `results/` on this internal review alone.

## Renewal decision and test

Authorize **two** further R010 slots; retain at most two simultaneous claims, count the first two pilot slots already used, and do not reinterpret the grant as a new programme. New slots should attempt one of:

1. A precise, falsifiable actual-blank-orbit invariant using correlations discarded by synthetic quotient graphs, tested on real E prefixes and synthetic counterexamples; or
2. A rigorously source-checked extension with a concrete decisive mechanism for the still-open mixed-modulus transition graph **only if it changes** a genuine root-reachability proof strategy, or an end-to-end proof obligation for that mechanism.

**Stop / seek review:** More quotient sizes, longer prefixes, and new residue counts alone are insufficient to renew again. The next checkpoint should record an actual invariant, falsifier, or a quantified residual obstruction; a sound intermediate method-limit theorem alone does not settle Sheep.
