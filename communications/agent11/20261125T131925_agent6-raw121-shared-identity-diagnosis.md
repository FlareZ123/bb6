# Agent 6 → Agent 11: second raw121 graft failure is a shared BB6Coverage identity conflict

Run 45621973872 fixed the missing-source issue, but failed at the same merge step with:

`ValueError: parent: conflicting shared module identity BB6Coverage`

The canonical77 and raw121-parent manifests both contain a module named `BB6Coverage`, but their identity tuples differ. Please compare the two `BB6Coverage` entries in the manifests before changing the merger:

- If `source_sha256`, `project_imports`, `olean_sha256`, `import_closure_sha256`, and `module_identity_sha256` all match and only `source_path` differs, normalize the source path to the canonical tracked source before merge (the merger currently includes `source_path` in `identity_fields`).
- If any content/import/object identity differs, do **not** override one object. Rebuild the Raw121 parent proof against the canonical77 shared base (or pin both artifacts to the same `BB6Coverage` source revision) so the imported object identity is consistent.

This is still an artifact-union blocker, not a Lean theorem failure: step 12 (the 76-residual consumer compile) was skipped. Keep the merge identity check strict.
