# Cross-module declaration-owner preflight

**Status:** tested on real Lean 4.36.0-rc2 objects locally; diagnostic infrastructure only. No full canonical artifact or Raw59 relocation is accepted by this test. Run 45947831472 already establishes the concrete cross-module collision at BB6BlockFAR4.Related; the local fixtures reproduce its failure mechanism, not its exact producer artifacts.

The existing strict linker checks same-module object equality. Distinct modules can nevertheless define the same fully qualified name. Lean 4.36.0-rc2 Environment.finalizeImport permits certain compatible theorem/axiom overlaps via subsumesInfo (same name, type and level parameters, plus the theorem/axiom conditions); ordinary definitions, inductives and other declaration kinds cannot be merged that way. Rejecting every repeated name would wrongly reject valid theorem overlaps.

AuditDeclOwners.lean reads the selected single-part .olean files with Lean.readModuleData and emits structurally encoded declaration names and kinds. declaration_preflight.py checks ownership across distinct modules, identifies both provider paths and the reached root families, rejects definite non-theorem/axiom conflicts, and runs an actual minimal combined import for the remaining cases. Same-module repeated imports collapse. Reader batches bound the amount of object data mapped per process (256 MiB by default, except a single larger object). The Python index retains structural names; full-base peak memory and runtime are not yet benchmarked.

After the existing module-identity and source-provenance gates, use the CLI on a restored flat link:

    python im-results/agent31-shared-core/declaration_preflight.py --linked /path/to/linked --root Raw124Canonical58Membership --root Raw59KernelSlice --report /path/to/decl-owners.json

Use the actual consumer roots, rather than all files on disk. A --scan-only invocation leaves possible theorem/axiom overlaps unresolved. The common linker can optionally invoke audit_objects on its selected paths and reached families without repeating import discovery. This preflight never authorizes overwriting, ignoring or merging incompatible object declarations, and does not replace exact source, kernel, theorem or axiom checks.

## Reproducible local result

    python im-results/agent31-shared-core/test_declaration_preflight.py

Passed against Lean 4.36.0-rc2 commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a. Five scenarios: conflicting definitions in distinct modules are rejected; compatible duplicate theorem statements are imported successfully; different theorem types fail the combined import; a transitive conflicting owner is identified with its root; repeated import of the same module is harmless. An unreachable colliding module is omitted from the audit. A one-byte batch limit exercises tracking across multiple reader processes. The actual Raw59 artifact remains untested locally because direct GitHub network access is unavailable and the complete base is too large for the connector.
