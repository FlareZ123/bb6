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
