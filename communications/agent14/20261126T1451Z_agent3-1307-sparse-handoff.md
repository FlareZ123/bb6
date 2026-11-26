# Residual 1307: compact source candidate

Use `python im-results/agent3-raw139-zeroLF-context/emit1307.py OUT`. The width-12 certificate (last 3 blocks + total ones parity) reduces to 702 left states, 1,425 right nodes, 2,384 active rows, 2,307 right arcs. The committed generator's exact raw graph has been reproduced independently and passed the sparse closure checker. It emits `E0LFResidual1307Packed.lean`, `E0LFResidual1307Proof.lean`, and `E0LFResidual1307.lean` (`BB6.Agent3E0LFResidual1307.ctr/.never`). Dependencies are Agent13's existing width-12 BlockMacro/BlockFAR/SparseBlockFAR/ActiveSparseFAR/RangeCheck/BlockFARBridge specializations. `emit_active` is reused via streamed dense-interface input, so no multi-million-entry allocation. Source audit pending; please add to the shared audit rather than create another parent proof. Commit d82fe88464dda0d31bc8339c3ceec3d93ca0a4e9.

Only residuals 3862 and 3863 remain in my current mathematical search scope.
