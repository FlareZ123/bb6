# A6 source-connected raw139 frontier refinement

Status: Lean 4.36.0-rc2 end-to-end compilation pending CI.

## Exact contribution

This module closes the missing source-import edge identified in the hard-root crosswalk:

1. It proves literal function equality between Agent19HardRoot.A6 and the pinned Cryptids BB6.F287.expectedRLE.
2. It imports CryptidsF287.literal_never and discharges NeverHalts A6 in the same Lean kernel as the accepted canonical-77 artifact.
3. It feeds that theorem through WeightedNonhaltLeafAdapter.forgetHaltRows_nonhaltCertificate, producing a WeightedTNFCertificate for the 25-completion A6 leaf at every bound.
4. It follows the existing eight remaining first-hole decisions from raw139 D1=0LC, uses the exact weighted halt-sibling checks at bound 7014, and closes only the A6 leaf.
5. It retains all 184 off-path ordinary siblings, replacing exactly the raw139 entry in the accepted 77-entry roster. The resulting explicit partial roster has 260 entries; the other 76 original parents are unchanged.

The result is a source-connected partial frontier at the existing global 7014 bound. It is NOT a closure of raw139, a reduction of BB(6) to a finite solved list, or an upper-bound proof for BB(6). All unresolved siblings remain explicit.

## Reproduction

The workflow downloads the exact canonical77-certified artifact from run 45554648116, checks out Google DeepMind Cryptids at commit c86f15861709b76042998c5211c7b2f83991621b, updates the upstream Mathlib/Verso pins from Lean 4.35.0-rc4 to 4.36.0-rc2, builds the original A6 machine theorem, and runs reproduce-a6.sh.

The script deliberately uses the Frontier.olean and related dependencies from the canonical77 artifact. It does not mix in the independently built raw117 artifact. The source-connected module is A6Ingestion.lean; its #print axioms reports are part of the CI log.
