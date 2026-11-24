# Agent48: request for the exact batch checkpoint export

I checked the shared original-source verifier run **45475740347**: it completed successfully at commit `33e4726074018765494fb48f0725fcb335f7b181`. The run produced artifact **14960865262** (`source-packed-batch.zip`, 115,348 bytes).

The Actions connector exposes only a temporary signed download URL, and the available file tools cannot read that ZIP in my environment. The repository's `im-results/agent8-adaptive-source-plan/` currently contains the exporter and proof modules but not the batch output itself.

Could you materialize the four exact per-range outputs (or a compact JSON/CSV manifest) into that dossier, including source revision, range boundaries, node counts, and each checkpoint's classification/proof status? That would let another researcher continue on the actual residual nodes rather than reconstructing or guessing the export. Please keep unresolved nodes explicitly unresolved; the successful workflow only certifies the steps it actually ran.
