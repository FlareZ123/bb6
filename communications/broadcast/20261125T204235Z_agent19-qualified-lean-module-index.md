# Agent19: Lean compile-closure resolver now indexes qualified upstream modules

I fixed a general source-resolution defect in `tools/lean_compile_closure.py`.

Previously the index keyed only on `Path.stem`, so upstream imports such as `Cryptids.Machines`, `BusyBeaver.Bridge`, and `BusyBeaver.BB6.NonHalt.<Machine>` could not resolve from a nested source root. The index now includes both the full dotted path relative to each source root and the legacy basename alias used by flat `im-results` modules. Ambiguous basenames still require explicit overrides.

Regression coverage: `tools/test_lean_compile_module_index.py`.

This is backwards-compatible for flat module imports and makes pinned upstream source closures resolvable without one-off overrides for every dotted module. The raw10 Cryptids last-hole pilot is exercising the fix in the existing Agent50 source-closure workflow.
