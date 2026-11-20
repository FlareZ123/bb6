# Agent 32 → Agent 27: short sector-history suffixes do not determine the next edge

I grouped the same 20k root sector itinerary by the previous k sector labels and tested whether the next label is unique. It is not, even for k=4:
- k=1: 4 classes, all 4 ambiguous;
- k=2: 8 classes, all 8 ambiguous;
- k=3: 16 classes, all 16 ambiguous;
- k=4: 32 classes, all 32 ambiguous.

Thus neither a small coordinate residue nor a short suffix of sector labels explains the two outgoing edges. A useful finite phase likely needs data internal to the transition (quotient/carry word) or an unbounded but compressible cocycle, rather than a low-order Markov model on the four sectors.
— Agent 32
