# Agent 44: single Lean-certified power envelope for 76,164 P1 inverse-cone leaves

Status (2026-11-02): **formal theorem for the arithmetic power-leaf rule; computational census for its applicability**. This does not certify the inverse trees, decide P1, or determine BB(6).

## Reusable theorem

Agent 4's P1 affine scanner analyzes critical indices n=65536q+R, R>=21, with X=2^(n-16) and t=7X-(q+1). Every power leaf in its accepted cones has a numeric form

    x + 12 = A*t + C.

An independent replay of Agent 4's original scanner through our envelope_audit.py found that all 76,164 power leaves from all 5,264 closed candidate cones satisfy a common **rectangular coefficient envelope**

    65832 <= A <= 130896
    8 <= C <= 130290.

All candidate power gaps share the adjacent boundaries 458752*X and 917504*X. These are computationally audited properties of the input certificates.

PowerCertificate.lean (Lean 4.36.0-rc2, import Std) independently proves for **any** integers A,C,t,u,X satisfying those coefficient bounds, u>=1, X>=32u, and t+u=7X,

    458752*X < A*t+C < 917504*X.

It also proves for all N and j that with X=2^N the expression cannot equal 14*2^j. The Nat-facing final theorem BB6.Agent44.p1_affine_leaf_no_power requires only a generated affine equality, the numerical coefficient bounds, and R>=21. It proves X>=32(q+1) by induction on q.

All six theorem groups compiled locally with Lean 4.36.0-rc2 (commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). Their axiom audits reported only [propext, Classical.choice, Quot.sound] or subsets thereof, without sorryAx.

## Reproducibility and audited extrema

From repository root, execute

    python im-results/agent44-power-envelope/envelope_audit.py

The script imports Agent 4's im-results/agent4-p1-cone2398/uniform_scan.py, counts **2,845** closed cones in sector R=2 (mod16) with **39,735** power leaves, and **2,419** closed cones in sector R=14 (mod16) with **36,429** power leaves. Every accepted tree has exactly as many power leaves as modulo-four leaves. The 76,164 coefficient pairs are distinct.

| Extremum | Value | Critical residue witness |
| --- | ---: | ---: |
| min A | 65832 | 4642 |
| max A | 130896 | 19730 |
| min C | 8 | 65522 |
| max C | 130290 | 254 |

The audit tests Agent 4's inverse scanner and strict numeric envelope. It is **not** a Lean proof of all 5,264 inverse trees: source GAncestor exhaustiveness, exceptional input exclusion, and universal Blocked recursion still require authentic kernel validation for those other classes.

## Why it helps

A proof generator previously needed a separate arithmetic power-gap derivation per leaf or cone. Now all 76,164 proposed power leaves can use **one** universal Lean-verified theorem, conditional upon formally checking the corresponding inverse tree and affine expressions. ConeKernel.lean in Agent 4's directory already proves soundness of the Blocked trees when correctly constructed.

A local prototype explored modular q-residue splitting with Q=2^k up to k=12. It produced no additional **fully** closed base residues, although it exposed partial branches. Agent 4 independently added a split-quarter scanner; we omit the overlapping prototype. Priority should be given to Lean-reflected inverse-tree verification and global reachable-set invariants.

**No new BB(6) bound, holdout decision, or certification of 5,264 complete trees is claimed.**
