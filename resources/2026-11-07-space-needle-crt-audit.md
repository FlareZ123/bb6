# Space Needle CRT classification audit

**Retrieved:** 2026-11-07  
**External repository:** [oohzaim1-afk/space-needle-100M](https://github.com/oohzaim1-afk/space-needle-100M)  
**Inspected commit:** `96e50a6ad829fa43e4ecfdf881b6679e599ef0b4`

## Finding: stale 17-element reference list

The external file [`laws/checkers/crt_obstruction.py`](https://github.com/oohzaim1-afk/space-needle-100M/blob/96e50a6ad829fa43e4ecfdf881b6679e599ef0b4/laws/checkers/crt_obstruction.py) computes prime-power discrete-log constraints for

[
q_a=2^{a+1}+3,qquad
r_a=(2a-3),2^{-1}pmod{q_a},
]

then combines the exponent congruences by generalized CRT. Its hard-coded `ref_ob` list contains 17 values:

`[1,4,9,10,13,19,21,22,23,24,25,26,31,32,33,39,40]`.

An independent reimplementation of the stated factorization, multiplicative-order, discrete-log, and CRT procedure finds **23** obstructed values for (1le ale40). The six additional values are

[
ain{7,12,18,28,35,36}.
]

Thus the hard-coded reference list is inconsistent with the algorithm it is intended to check and appears stale. This audit does not establish that every other summary statistic in the external repository is wrong. In particular, the separate claim of 96 obstructions among 120 valuations has not been independently rechecked here and should be treated as unverified pending a fresh run.

## Reproducible CRT certificates

The external exponent variable is (j=k+1). The local terminal-feeder equation uses (n=k+2=j+1), so the table gives both the prime-power orders and the required (n)-residues.

| (a) | (q_a) factorization | ((p^e,operatorname{ord}_{p^e}(2),j)) | Incompatible (n=j+1) conditions |
|---:|---|---|---|
| 7 | (259=7cdot37) | ((7,3,1),(37,36,29)) | (nequiv2pmod3), (nequiv30pmod{36}); residues disagree modulo 3 |
| 12 | (8195=5cdot11cdot149) | ((5,4,3),(11,10,4),(149,148,80)) | (nequiv4pmod4), (nequiv5pmod{10}); residues disagree modulo 2 |
| 18 | (524291=29cdot101cdot179) | ((29,28,1),(101,100,81),(179,178,122)) | First two give (nequiv282pmod{700}), incompatible with (nequiv123pmod{178}) modulo 2 |
| 28 | (536870915=5cdot7cdot1901cdot8069) | ((5,4,2),(7,3,1),(1901,1900,405),(8069,8068,5975)) | First two give (nequiv11pmod{12}), incompatible with (nequiv406pmod{1900}) modulo 4 |
| 35 | (68719476739=61cdot523cdot2154013) | ((61,60,6),(523,522,502),(2154013,2154012,190420)) | (nequiv7pmod{60}), (nequiv503pmod{522}); residues disagree modulo 6 |
| 36 | (137438953475=25cdot154543cdot35573) | ((25,20,17),(154543,77271,5191),(35573,35572,3759)) | First two give (nequiv468818pmod{1545420}), incompatible with (nequiv3760pmod{35572}) modulo 4 |

All displayed factorizations were independently checked by exact multiplication and primality tests. The listed multiplicative orders and discrete logarithms were independently recomputed; each discrete-log witness was checked by modular exponentiation.

Direct enumeration of powers of 2 modulo (q_a) also confirms non-membership for (a=7,12,18), with respective orders 36, 740, and 62,300. The remaining three certificates use the displayed prime-power order constraints and CRT incompatibilities.

## Lean formalization

The repository's `im-results/agent48-space-needle/SpaceNeedleObstructionFamilies.lean` now formalizes the composite-modulus obstructions for (a=7) and (a=12), using the source-certified terminal-feeder modular identity. The proofs show why checking each prime factor independently is insufficient: each factor admits a power-of-two residue, while the required exponents cannot be reconciled.

The cases (a=18,28,35,36) remain computational CRT certificates in this audit and are not claimed as Lean-proved.

## Interpretation

This correction concerns the external finite modular classification of synthetic terminal feeders. It does not establish that any such feeder is reachable from the blank-root state, and it does not resolve the Space Needle halting question or BB(6).
