# Canonical three-parent certificate graft

The raw71, raw77 and raw81 source audits succeeded independently at weighted bounds 395, 7014 and 7014 respectively: [raw71](https://github.com/FlareZ123/bb6/actions/runs/45530141516), [raw77](https://github.com/FlareZ123/bb6/actions/runs/45530867702), [raw81](https://github.com/FlareZ123/bb6/actions/runs/45531218803). Each covers all 25^5 completions of its own partial table.

The new `CanonicalThreeParent.lean` consumes these theorems through `graftRoster_sound` and exposes a reusable `prune_sound` for any 7014 quotient roster. Its two concrete cuts target 78→75 and 76→73 (the latter explicitly assumes the raw107 and raw114 parent bounds). The counts follow from the manifest census, but the new integrated source audit has not yet passed. Exact BB(6) remains conditional on all retained Covers at B.

The existing raw81 manual workflow target `canonical-three-parent` regenerates all needed sources at a single checkout, compiles the original import closure and records the source/import/olean manifest. It does not mix potentially incompatible binary artifacts.
