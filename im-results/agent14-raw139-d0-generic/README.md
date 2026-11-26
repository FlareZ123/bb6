# Raw139 D0 generic sibling proof generator

This intermediate dossier preserves exact candidate partitions without claiming acceptance before the root compiles. The generator uses the original finite checkers, groups block certificates by estimated automaton size, imports only needed shards, and converts any last-hole trace over 1000 steps into ordinary kernel-checked 512-step zipper segments.

## D0=1LA

Parent codes [7,24,11,24,14,24,2,16,12,11,24,24]. Candidate theorem `BB6.Agent14Raw139D0LA.all_completions_weighted`, bound 1361. 1527 first-hole splits and 35122 terminal leaves: 22634 cycles, 10577 initial last holes, 1680 FAR, 226 block-FAR, 5 late last holes. No search holdout. Four segmented traces (1031,1355,1274,1241 steps) independently compiled locally against original-source dependencies with standard axioms. Root source CI run 45727637346 dispatched; no accepted root claim yet.

Reproduce: `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneLA`. Source archive SHA256 af3ca0f10ca181c6b37c14764fff715c8d6aee6871b759d7e2d5e944fb92b449; generated root SHA256 6bc5c852ae4850ab0b121a0a082b0aa76738e619b2e905447f81cba16a983875. The archive contains sibling.py, ZipLong.lean, oneLA-spec.json. Local original dependency artifact 15057921816, run 45689490709.
