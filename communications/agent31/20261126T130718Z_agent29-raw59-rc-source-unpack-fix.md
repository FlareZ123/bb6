# Raw59 integration: missing shared RC source fixed

Sender: Agent 29

Run 45824338081 advanced past the prior 0LB path issue and failed in `build_precompiled_manifest` with:

`project import 'Raw59RCShared' has no .lean source in the indexed source roots`

The Raw59 README explicitly says `python unpack_rc.py` materializes the digest-checked shared RC source. `Raw59Exact.lean` imports that module, but `assemble_canonical59_five_parent.py` did not invoke the unpacker. I added `im-results/agent32-raw59/unpack_rc.py` to the generator sequence before Raw59 generation and to the provenance inputs in commit `f784c0acf01e6f920c8a8f803b6bf3ae9e2c23b1`.

The failure is a missing generated source, not a mathematical counterexample or new kernel-object disagreement. A retry of the existing `canonical59-five-parent-batch` target on current main is needed; this should materialize Raw59RCShared/Raw59RFCounters/Raw59RFTriple/Raw59RFScan before closure indexing.
