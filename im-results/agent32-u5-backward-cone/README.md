# U5 mixed-64 backward-cone exclusion

**Status: Lean source draft; exact-source preflight and the extended M32 workflow are pending. No new theorem is yet claimed as CI-certified.**

## Objective

The only unresolved parent depth in Agent 3's U5 cylinder z ≡ 17 (mod 64) is d=1. Its parent equations give, for z=17+64u,

a = 32022 + 115584u,  k = 174637 + 630336u,

so a ≡ 22 (mod 64) and k ≡ 45 (mod 64). The intended source-level theorem is:

∀ a,k, a ≡ 22 (mod 64) ∧ k ≡ 45 (mod 64) → ¬ Reach_CLine(a,k,0).

The proof does not construct a new finite quotient. It uses the existing kernel-checked M32 certificate only for three exceptional cells.

## Backward-cone invariant

For a CLine state (a,k,c), define:

- T0: c=0, a ≡ 22 (mod 64), k ≡ 45 (mod 64).
- T1: c=1, a ≡ 22 (mod 64), k ≡ 44 (mod 64).
- T2: c=3, a ≡ 22 (mod 64), k ≡ 42 (mod 64).
- Main: c≥4, c≤a, a ≡ c+19 (mod 64), k+c ≡45 (mod 64).
- Side: c≥4, a≤c, c ≡ a+46 (mod 64), a+k ≡30 (mod 32).

Bad is the union of these five cases. The exact CLine predecessor analysis is intended to establish:

nextC(s)=t ∧ Bad(t) → Bad(s) ∨ Forbidden(s),

where Forbidden means c=0, a ≡31 (mod 32), and k ≡5 or 21 (mod 32).

The high-branch predecessor preserves Main or Side. The two exceptional cases are:

1. A Main target with k=2 has a c=0,a=0, even-counter predecessor which satisfies Side.
2. A Side target with k=1 has a c=0,a≥2 predecessor in Forbidden. Its coordinates are (a+2,(c-1)/2,0); the Side congruences and c≥a force the quotient residues a+2 ≡31 (mod 32) and (c-1)/2 ≡5 or 21 (mod 32).

All other special c=0 predecessor clauses are excluded by the defining residues/parities. The blank initial state (5,0,1) is not Bad. Therefore, if the predecessor lemma and M32 Forbidden theorem compile, induction on BB6CLine.Reach proves original_no_22_45.

## Existing M32 certificate reused

M32U5Cells.lean wraps the existing CSourceBridge32/CCert theorem. For a ≡31 (mod 32), the M32 quotient coordinate is 31. For k ≡5 (mod 32), its quotient coordinate is either 5 or 37; for k ≡21 (mod 32), it is 21. The cells

- (31,5,0)
- (31,21,0)
- (31,37,0)

are all absent from the M32 reachable set. The wrapper uses q_congr_big, q_choices, reachable_seen, and source_reachable_embeds32; it does not use native_decide.

An independent V8 reconstruction of the exact nine CLine clauses reproduced the M32 census: 31,570 reachable quotient states and 189,834 representative edges. It also found all three cells absent. This is computational corroboration; the intended proof authority is the M32 Lean certificate.

## Relation to Agent 3's U5 parent fan

For z ≡17 (mod 64), the four z mod 256 lifts have the following M32 projections:

| Parent depth | M32 parent cells | Status in M32 |
|---|---|---|
| d=0 | (30,12,0) | absent |
| d=1 | (22,13,0) | seen |
| d=2 | (36,19,0) or (36,35,0) | absent |

Thus only d=1 needs the new backward-cone argument. The earlier 156,816-state A/K64,C32 quotient would exclude this cell, but the source-only predecessor invariant is smaller and avoids a new quotient certificate.

The z ≡20 (mod 32) cylinder (w ≡45 mod 128) is already covered by the existing M32 source certificate at d=0,1; no A/K32,C32 certificate is needed. The d=0 and d=2 parents for z ≡17 (mod 64) are also already M32-absent.

## Files and verification plan

- M32U5Cells.lean: three exceptional M32 cells and original-CLine nonreachability wrapper.
- M32U5Backward.lean: Main/Side/Bad predecessor invariant and the intended theorem original_no_22_45.
- .github/workflows/agent43-c-quotient32-kernel.yml: extended after the existing M32 source bridge to compile these two modules in the same M32 certificate run.

The current invocation's local shell is unavailable. A focused local Lean preflight has been requested from Agent 15 and from Agent 4 (who recovered Lean 4.36.0-rc2). The workflow has been extended but not dispatched pending that preflight. After preflight, run the existing manual M32 workflow once and inspect the #print axioms output for both exported theorems. Then compose original_no_22_45 with Agent 15's m32_section_reach_embeds and Agent 3's exact U5 parent fan to establish the complete w ≡101 (mod 128) source exclusion.

Until that composition is compiled against the exact source import closure, this remains a draft. It does not solve BB(6), the complete Machine C stopping criterion, or the remaining U5 families.
