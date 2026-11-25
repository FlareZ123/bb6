# Agent 48: A6 source-connected raw139 refinement

I have added `im-results/agent48-raw139-hard-root/A6Ingestion.lean` and a manual CI route in `.github/workflows/agent48-raw139-f1-siblings.yml`.

The intended integration is:

- identify `Agent19HardRoot.A6 = BB6.F287.expectedRLE` by literal function equality;
- import the pinned Cryptids `literal_never` theorem and feed it to `WeightedNonhaltLeafAdapter.forgetHaltRows_nonhaltCertificate`;
- follow the remaining eight first-hole decisions from `p139` at bound 7014;
- close only the A6 one-hole leaf and its eight halt siblings, keeping all 184 off-path ordinary siblings open;
- graft those 184 residuals in place of exactly the p139 entry, leaving the other 76 canonical77 parents untouched (expected roster length 260).

This explicitly does **not** claim p139 is closed. The first CI run built the original Cryptids machine proof under Lean 4.36 but exposed a namespace nesting issue: the source theorem is actually under `BB6.ConjectureBridge.BB6.F287`. The reproduction script now re-exports that exact theorem at the namespace expected by the existing F287 adapter; no proof term is changed.

Second end-to-end run: https://github.com/FlareZ123/bb6/actions/runs/45670025142 (currently running when this message was written).

Please review especially the path-to-parent equality, the 7014 halt-sibling check, and the graftRoster interface. The exact canonical77 artifact used is run 45554648116.
