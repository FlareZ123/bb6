# Raw139 D0 generic sibling proof generator

This intermediate dossier preserves exact candidate partitions without claiming acceptance before the root compiles. The generator uses the original finite checkers, groups block certificates by estimated automaton size, imports only needed shards, and converts any last-hole trace over 1000 steps into ordinary kernel-checked 512-step zipper segments.

## D0=1LA

Parent codes [7,24,11,24,14,24,2,16,12,11,24,24]. Candidate theorem `BB6.Agent14Raw139D0LA.all_completions_weighted`, bound 1361. 1527 first-hole splits and 35122 terminal leaves: 22634 cycles, 10577 initial last holes, 1680 FAR, 226 block-FAR, 5 late last holes. No search holdout. Four segmented traces (1031,1355,1274,1241 steps) independently compiled locally against original-source dependencies with standard axioms. Root source CI run 45727637346 dispatched; no accepted root claim yet.

Reproduce: `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneLA`. Source archive SHA256 af3ca0f10ca181c6b37c14764fff715c8d6aee6871b759d7e2d5e944fb92b449; generated root SHA256 6bc5c852ae4850ab0b121a0a082b0aa76738e619b2e905447f81cba16a983875. The archive contains sibling.py, ZipLong.lean, oneLA-spec.json. Local original dependency artifact 15057921816, run 45689490709.

## D0=1LF

Parent codes [7,24,11,24,14,24,22,16,12,11,24,24]. Candidate theorem `BB6.Agent14Raw139D0OneLF.all_completions_weighted`, bound 42038. 1242 splits, 28567 terminal leaves: 19544 initial cycles, 7060 initial last holes, 1682 FAR, 263 block-FAR (including two width-four cases), one late cycle and 17 late last holes. No search holdout. Long queries 42032,1225,1255 steps are segmented in the generated Long module. Original width-four specialization is reused from Agent13/Agent32; no new semantic assumption. Namespace OneLF is distinct from existing zeroLF's LF namespace.

Reproduce: `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneLF`. Source archive source-v2.tar.xz.b64 SHA256 d7df8ff3f2e38cef9e24e56e754163eabac7792d4da5d452e5416bcfec2db924; generated root SHA256 b9da28e853bcf3b37606453d488ff2bb6a8f7a52216aa2702f9b99f3e8f01c57. Source audit dispatched run 45728113457. Root and long trace acceptance pending.

## D0 = 0RC (candidate, source audit pending)

Exact table `[7,24,11,24,14,24,9,16,12,11,24,24]`, candidate bound 775. The partition has 998 splits and 22,955 leaves: 13,935 initial cycles, 5,551 initial last holes, 3,113 FAR, 351 block FAR, two late cycles and three late last holes (maximum query 769). No search holdouts. The root SHA-256 is `41b6b03422798ffc4f3325cbe49fa8fdd0d1c6449e1f282852e103d6655c5fe0`. Reproduce with `bash reproduce.sh ZeroRC` from repository root using the full path to this script. Exact-source audit dispatched from `90c3c382991bd530d06a9c81bbfbeec3de38a7d2`. This is not yet an accepted theorem.

## D0 = 1RF (candidate, source audit pending)

Exact table `[7,24,11,24,14,24,23,16,12,11,24,24]`, candidate bound 6250. The initial partition has 2673 splits and 61,480 leaves: 40,979 initial cycles, 14,247 initial last holes, 5,553 FAR, 676 block FAR, two late cycles and 23 late last holes (maximum query 6244). No search holdouts. 299 generated Lean modules. Reproduce from repository root with `bash im-results/agent14-raw139-d0-generic/reproduce.sh OneRF`. Root SHA-256 `6ca0dc341acf0aa3c54fb4e3ddbf277476829c6681d16b840ff85f5cf1cfccc5`; CI run 45729425638. This is not yet an accepted theorem.
