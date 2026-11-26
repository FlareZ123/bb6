# Raw10 original rectangle 16

**Computational classification complete; local Lean exact lower bound 7376 accepted; upper-bound compilation in progress.** Domain mass 3,515,625. Independent of external holdout premises. Exact encoded-domain identity in Box16Core.lean. Bound witness [8,0,11,6,17,13,11,13,2,24,20,5], 7373 live steps + 1 halt + attainable blank delay 2. Box16Lower.lean proves lowerBound with standard axioms.

The initial first-hole partition: side-cycle mass 1,468,475, unresolved mass 974,025, halting 530,818, relative cycle 483,675, all ordinary 58,632; sum 3,515,625. Of 1,041 open cylinders, 997 admit bit-window invariants and 38 admit lag-periodic RLE invariants. The other six first consult their unique open A1 slot after 257, 298, 439, 1379, 7139, or 7373 live steps. If ordinary A1, the table is fully ordinary and cannot halt; otherwise the exact halt is witnessed. Compression yields 1,035 certificates, 57,414 joint states (largest 2,200). The generated proof has 61 certificate groups and 496 compositional modules. New generic DomainPackedStack.lean separately proves that one finite stack certificate may cover an entire product of allowed transition sets (standard axioms).

## Reproduce

From this directory, set PYTHONPATH to ../agent13-raw10-box17 and run python box16.py; python box16_ngram.py; python finish16.py; python gen16.py. Compile box16lean/Box16Direct.lean with tools/lean_compile_closure.py after unpacking original source dependencies. Box16Direct.exactWeighted is the generated theorem target, currently awaiting the full local build. No global canonical-count change.
