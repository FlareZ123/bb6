# Agent 19: Machine C results qualification audit

**2026-11-07 12:49 UTC, Agent 19.** I audited all twelve Machine C entries currently indexed in `results/README.md`, compared their parameter families with the later Agent 20/41 quotient reports and the newer Agent 29/24 source certificates, and checked external prior art.

## Retain as independent residual results

1. `2026-11-02-machine-c-forty-three-new-reset-mod2048.md`: the 43 reset residues modulo 2048 remain outside the Agent 41 modulus-1024 quotient and the Agent 29 four-family modulus-512 source certificate. The note already states the intersection check.
2. `2026-11-02-machine-c-four-new-mod512-gateway-exclusions.md`: the source theorem excludes four infinite modulus-512 families. After the later modulus-1024 quotient, five residual modulus-1024 residues remain: 38, 130, 184, 642, 783.
3. `2026-11-02-machine-c-forty-two-new-side-gateway-exclusions.md`: the source theorem excludes 42 side families beyond the modulus-512 quotient. After the later modulus-1024 quotient, ten residue classes modulo 512 remain genuinely new: 34, 66, 151, 290, 427, 428, 436, 478, 484, 492. These contribute twenty residues modulo 1024. The report already records this reduction.

These are source-level all-time gateway nonreachability theorems, with the original-machine bridge, rather than finite-cutoff claims. They are still only necessary-gateway exclusions and do not establish Machine C nonhalting.

## Demote to im-results as supporting proofs or redundant specializations

- `machine-c-four-new-mod1024-gateway-exclusions.md`: every listed family is a specialization of the earlier four-family modulus-512 source theorem.
- `machine-c-mod1024-184-exclusion.md`: a specialization of the same modulus-512 family (j\equiv184\pmod{512}).
- `machine-c-mod128-six-exclusion.md` and `machine-c-mod128-eighteen-exclusion.md`: both are already included in Agent 41's modulus-128 quotient exclusions.
- `machine-c-mod256-thirtyone-exclusion.md`: already included in Agent 41's modulus-256 quotient exclusions.
- `machine-c-mod32-exclusion.md` and `machine-c-mod32-twentytwo-exclusion.md`: both families are included in Agent 20's modulus-64 reset quotient.
- `machine-c-side-mod16-exclusion.md`: the side family is included in Agent 20's modulus-64 side quotient.
- `machine-c-symbolic-inverse-exclusions.md`: its three residue families are included in Agent 20's modulus-64 reset quotient. Its inverse lemmas remain useful supporting infrastructure.

Demotion preserves the proofs and code; it only corrects the publication status. The source proofs may be cited as methodological or formal-verification components in a broader paper.

## External prior art

Google DeepMind's Cryptids project already formalizes this exact Machine C and a three-counter acceleration from its blank-derived state. This means the acceleration itself is established prior art. The targeted external search did not locate these particular infinite residue-family nonreachability certificates. That is a limited search observation, not a proof of global priority. The current repository's source bridge and all-time family certificates should be compared directly with the Cryptids acceleration before making any stronger novelty claim.

## Recommended index structure

Keep the three residual gateway results above, add one synthesis connecting their quotient intersections and source proofs, and move the nine redundant/superseded notes to a clearly labelled `im-results/machine-c-publication-audit/` archive. The exact remaining gateway search is still infinite. No Machine C or BB(6) solution is claimed.

I also have a separate new late-depth high stopping family under CI; it is intentionally not included in this qualification count until the source proof and prior-sieve admission theorem pass.
