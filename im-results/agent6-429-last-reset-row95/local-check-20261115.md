# Lean 4.36.0-rc2 local check — 2026-11-15

This is an intermediate verification record, not a research result and not a full dependency-closure certificate.

## Runtime

The split archive parts in the conversation were concatenated:

```sh
mkdir -p /tmp/lean
cat /mnt/data/lean-4.36.0-rc2-linux.zip.{001,002} > /tmp/lean.zip
unzip -q /tmp/lean.zip -d /tmp/lean
tar --zstd -xf /tmp/lean/lean-4.36.0-rc2-linux.tar.zst -C /tmp/lean
export PATH="/tmp/lean/lean-4.36.0-rc2-linux/bin:$PATH"
lean --version
```

The ZIP contains a `.tar.zst`, so the additional `tar --zstd` extraction is required. The Lean runtime reports 4.36.0-rc2. The shell could not clone the GitHub repository (network unavailable); source files were obtained through the GitHub repository connector and staged locally.

## Successfully compiled actual modules

Using the branch sources and Lean 4.36.0-rc2:

1. `BB429Rank`
2. `BB429Mod8`
3. `BB429RootEven8`
4. `BB429NewResidue` (including the actual `odd_back`, `even_back`, and `reach_allowed`)
5. `BB429RootOddRowsStrong` — the actual file, including `rooted_not_13_1` and `rooted_not_5_1`
6. `BB429LastResetRow95` — the actual file, including all three branch-10 consumer theorems and the corrected 16-pair d-mod64 cases
7. `BB429InverseKernelExtended` — the actual file, including all three new `Bad` branches and their `bad_sound` cases
8. `SourceLastResetRow95` — the actual wrapper file

## Deliberate stubs and limitations

- `BB429NewRootRows` was stubbed as an empty import while compiling `BB429RootOddRowsStrong` and `BB429LastResetRow95`; neither actual file uses declarations from that module.
- The kernel check used interface stubs for the unchanged `BB429RootMod16`, `BB429RootMod32`, and `BB429NewRootRows` theorem interfaces. Thus it checks the new `Bad` soundness branches against the real new root theorems, but is not a full kernel dependency closure.
- The source-wrapper check used a stub for the unchanged `SourceMod16.source_run_to_local` theorem with its actual equality signature. It does not verify the pinned Cryptids source transport.
- A local attempt to compile the actual `BB429NewRootRows` module exceeded the shell's 300-second timeout. The module is unchanged and had compiled in the existing root-row workflow before that workflow reached the new root-strong file. Attempts to compile temporary copies of RootMod16/32 were not used as evidence; those unchanged modules remain to be checked in the full workflow.
- No GitHub Actions run was dispatched. Critic's compile-first gate is not yet fully satisfied.

## Bug found and fixed

The first local kernel check exposed failure to synthesize `Decidable (Bad s)` using the previous one-line unfolding. The repository file now explicitly supplies the decision procedure for the nested `BB429Mod8.Allowed s.a s.b` proposition before synthesizing `Decidable (Bad s)`. The modified kernel then compiled under the stated interface stubs.

## Next full check

Compile the real `BB429NewRootRows`, `BB429RootMod16`, and `BB429RootMod32` modules, then compile `BB429InverseKernelExtended` with no stubs. Finally run the prepared pinned source-chain workflow to compile `SourceLastResetRow95` against the actual Cryptids source. Do not treat this record as evidence of BB(6) or a complete decision of machine #429.
