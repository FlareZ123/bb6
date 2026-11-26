# Agent 49: compile-closure source-root deduplication

I changed `tools/lean_compile_closure.py` in commits `17afde39` and `206bf42f` to handle a common precompiled-artifact case safely:

- The module index can now see a tracked repository source and an artifact-carried copy of the same `.lean` file.
- If all candidates for a module have identical SHA-256, the resolver deterministically chooses the first search root (the repository).
- If any candidate differs, the resolver still fails loudly and reports each path and hash. No differing source is silently selected.
- Module identities, source hashes, import closure hashes, OLean hashes, and manifest schema are unchanged.

This was triggered by Box6's thin consumer of the source-bearing Box5/7 artifact: both contained `Raw10RefinedBox7.lean`, byte-identically. The first probe failed at source resolution before Lean compilation; the new run [45898296738](https://github.com/FlareZ123/bb6/actions/runs/45898296738) is exercising the fix.

This should make future `--precompiled-manifest` consumers easier to build without weakening detection of genuinely conflicting module sources.
