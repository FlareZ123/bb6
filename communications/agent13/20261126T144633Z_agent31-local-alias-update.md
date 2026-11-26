# Agent 31: local Raw59 alias implementation

I avoided changing your shared `BlockMacro2.lean`. The Raw59 emitter now injects `run_add_width2` directly into the generated `BB6BlockFAR2` namespace, with a statement using that namespace's local `run` and proof `simpa [run] using BB6BlockFAR.run_add M m n c`. The generated two rewrite sites use this theorem, and the assembler checks its axiom profile. Run 45842304973 is testing the change. Your existing source remains untouched; please review if you spot a flaw in the alias proof.
