# Raw36 D1=1LA: cross-parent FAR reuse

This is an intermediate exact-table investigation, not a complete parent Cover.

The saved canonical census from run **46122807180**, artifact **15254284649**
has parent `1RB---_1RC---_0RD---_0LD1LA_------_------`, weighted candidate
bound **1015**, and **3841** exact OPEN one-hole literal tables (census gzip
SHA256 `cb699136a90a91f972542cdd62aa1340d42e58c39dfff867dce5e84444da7866`).

Taking the **441 distinct FAR winner automata** from neighboring D1=0RE
recovery run **46153748009**, artifact **15266667082** (its `found.tsv`
SHA256 `ed56aa2f9f27a140ad580d3b6f88a8bcfc70a5479eb32fdb29489663b0bdad67`),
and replaying only those finite automata on the 3841 D1=1LA literals closes
**2345 exact literals**, leaving **1496**. There are **265 distinct winner
automata** on D1=1LA. The deterministic table/code mapping SHA256 is
`93d0c64957cdf26a0458e88c8e829d747d3b6d01257055ce41b511f0b6430eb5`.

Coverage by FAR state count is d=4: 48, d=5: 308, d=6: 263, d=7: 213,
d=8: 294, d=9: 450, d=10: 765, d=11: 4. Thus the reused bank candidate-closes
61.05% of the saved OPEN roster without another canonical tree search.

`seed_reuse.cpp` is the seed-only exact FAR evaluator. `derive.py` pins
both input artifact hashes and the output mapping hash. `emit.py` turns a
selected state-cap or mapping subset into original Lean `farSound` theorems.

Local Lean 4.36.0-rc2 source checking has accepted the first **40** d≤8
literal theorems in one generated module. Their mapping prefix SHA256 is
`5e4a5e6302f8b308791b792f3c4c23ae87bea61bbc5c34e98d796eed6546d020`;
generated source SHA256
`11492096378df14306fba24394377a1a7efd7f2f4cf73a23d62c7490be164159`;
olean SHA256
`103f691d1708a643c5fab49bec8a02ccc77807bff9adc2cb69d5940502b89809`.
Every printed theorem depended only on
`[propext, Classical.choice, Quot.sound]`.

No D1=1LA parent Cover or Raw36 global decrement is claimed here. The next
high-value step is a balanced source gate over the reused bank, followed by
composition into the saved canonical D1=1LA audit tree.


## Structured quotient transfer: 153 candidate holdouts

The 27 distinct regular-stack parameter families actually used by the
neighboring D1=0RE structured-candidate artifact (run **46154479283**,
artifact **15266524122**, `structured.json` SHA256
`a56b0a2558ee5576ce2de4f40069a39349d06e10764ea4aec70a29ed2c9c5560`)
were replayed sequentially on the **1496** D1=1LA literals left after the FAR
reuse above.  They close another **1343 exact literals**: 1102 modular
summaries, 229 run-length summaries and 12 periodic summaries.  Exactly
**153** literals remain.  The 1343-row mapping SHA256 is
`4f65305134b5151243d7b1ae61ae1582bc4b25f0298d65ded52680999e7c9b8d`;
the sorted 153-line holdout file SHA256 is
`6efc697700bd538cdd552bfa35913ba7e3cbb6df38aeda10c78225f5371af8d5`.

Thus the two inherited proof families candidate-close **3688 / 3841
(96.0167%)** of the saved canonical D1=1LA OPEN roster, leaving only 153 for
new structural work.  This is a finite exact-key statement about the saved
canonical frontier; it is not yet a whole-parent Cover.

As an independent source check, the **24 lowest-replay-state** structured
records were regenerated with the repository's incidence-quotient emitter and
compiled locally under Lean 4.36.0-rc2 against the accepted
`TwoSidedAutomata` dependency closure.  All 24 `never` theorems reported
only `[propext, Classical.choice, Quot.sound]`.  Generated source SHA256:
`c90afb6f31a684f9407e888ef6172a6e4ee58f68db3f64ce1bd4817e401615ca`.

`reuse_structured.py` deterministically reproduces the 1343/153 split from
the three pinned inputs.  `emit_structured.py` regenerates independent Lean
certificates for any desired low-state prefix or the full structured bank.
The earlier eight-worker local replay was memory-wasteful; the sequential
replay completes comfortably and is the reproducible path.


## FAR mutation shell: 122 candidate holdouts

Starting from the 153 exact residual literals above, one-transition mutations of
the 441 inherited D1=0RE FAR seed automata close **31 additional exact
literals**.  Exhaustive rooted binary DFAs through **d=5** close none beyond
that mutation shell.  The 31-row table/code mapping SHA256 is
`3ab7b9423dc3a1d9c428144c6daa9e632c8c13812997a04ef45589f1c58ddd10`;
the sorted **122** residual table list SHA256 is
`eca0fc8bd3a486f45cbbef0445dbd4f491d3117712b5400523c674bc4a07a273`.

All 31 new FAR witnesses were regenerated as original Lean source in seven
small modules and kernel-checked locally with Lean 4.36.0-rc2 against the
accepted `ThreeHoleAudit` / `FastFAR` dependency closure.  Every `never`
theorem reports exactly `[propext, Classical.choice, Quot.sound]`.  A second
mutation shell seeded by the new 31 winners closes **zero** of the 122, and
exhaustive d≤5 FAR likewise closes zero, so this specific FAR neighborhood is
exhausted.

Combined with the inherited FAR and structured families, only **122 / 3841**
saved D1=1LA canonical OPEN literals remain outside the current exact
certificate banks.  This is a 96.824% candidate reduction of the OPEN roster;
whole-parent Cover status still awaits source checking/integration of the full
structured bank and proofs for the 122 true holdouts.


## Late-hole weighted leaves: 98 unresolved

Of the 122 exact tables left after the FAR mutation shell, **24** reach their
only unassigned row `F0` at steps **2155 through 2479**. At uniform local
bound **2600**, all 24 pass `ZipThreeHoleAudit.zipCheck` as `.last` leaves
and yield `WeightedTNFCertificate 2600` objects. The exact source is checked
in `Raw36D112Last00.lean` through `Raw36D112Last03.lean` (six leaves per
module). Local Lean 4.36.0-rc2 compiled every module; every `checked` and
`weighted` theorem reports only `[propext, Classical.choice, Quot.sound]`.
The four source SHA256 values are
`296899b3f54252187975a12cd27392ececd7bb4e5f650d9aa012e1bf4c1409ed`,
`7ef8e86a501da90488891314286af66f26337f1b75a085b7fe89d1f7bd69907d`,
`65f028836db95e5bef1c1fd66a4ef1487723b51f4ca480f4132edc2c47ae0aee`,
and `759d9d2e2e2d46034643a8ee51384fd80051af3fdb69077cc789d160ce27131c`.

Consequently **98 / 3841** exact D1=1LA OPEN tables remain outside the current
FAR, structured-quotient, and late-hole weighted banks. This is a genuine
weighted-certificate reduction. Whole-parent Cover status still needs full
structured-bank integration plus proofs for those 98 residual tables.


## Generic structured sweep: 95 unresolved

Extending the structured parameter bank from the 27 inherited D1=0RE winners
to the repository's generic run-length and modular motifs finds **three**
additional exact D1=1LA nonhalting leaves:

- `1RB0LE_1RC1RB_0RD1LF_0LD1LA_0LB1LC_---0LA`: `["r",4,4,4,192]`
- `1RB1LA_1RC0RE_0RD1RB_0LD1LA_---1RF_1RA0LF`: `["r",3,2,4,140]`
- `1RB1LC_1RC1RA_0RD0LE_0LD1LA_---0LF_0LB0RA`: `["r",3,2,4,579]`

All three were regenerated through the independent incidence-quotient emitter
and kernel-checked by Lean 4.36.0-rc2; each `never` theorem reports exactly
`[propext, Classical.choice, Quot.sound]`.  The generated source SHA256 is
`e317beb729a592edc278574e78fa4e0ee1201126d12dd03d8e1f08e000acaa2f`
and olean SHA256 is
`650e5ccfabb8983c6850c0417eb16061a0608a3fb46d7c7abc68e9b16dc05789`.
`generic_extra3.tsv` and `emit_extra3.py` reproduce the exact source.

After the inherited FAR bank, inherited structured bank, 31 FAR-mutation
leaves, 24 late-hole weighted leaves, and these three generic structured
leaves, **95 / 3841** exact D1=1LA canonical OPEN tables remain unresolved.
