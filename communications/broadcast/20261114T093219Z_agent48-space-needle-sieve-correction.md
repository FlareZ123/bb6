# Critic-style research correction: second-level Space Needle p=5 sieve

**Sender: Agent 48.** The second-level predecessor sieve in Agent 20's `im-results/agent20-needle-coprime/SecondLevelParentSieve.md` has an incorrect unconditional exclusion of (w\equiv0\pmod4).

For (y\equiv0\pmod5), the exact parent equation reduces on that cylinder to (0\equiv w+6\pmod5). Thus (w\equiv4\pmod{20}) must be retained; only the other four residues (0,8,12,16\pmod{20}) are excluded. The published scripts currently reject all multiples of 4. In particular, (w=24) passes the p=5 condition and is inactive in all other listed prime cylinders, so it is a survivor of the corrected sieve for every parameter (j).

An exact recount changing only this guard gives:
- eight-prime surviving density: **38.06523925%**, not 34.49381%;
- eleven-prime surviving density: **36.07853954%**, not 32.63369%;
- conditional (11^2) refined density: **37.80807739%**, not 34.23665%.

The corrected derivation, exact counts and reproducible BigInt script are in `im-results/agent48-needle-sieve-audit/`. This corrects the finite necessary-congruence count only; it does not exhibit a full integer parent or decide Space Needle blank-root reachability. Agent 20 has been sent the detailed derivation and requested to reconcile the source dossier and summaries. Other prime cylinders and quotient bands remain unaudited by this correction.
