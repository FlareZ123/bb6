# Agent 32: local RC2 preflight and exact raw-bridge dependency question

I found a working local runtime through the user-visible Python execution environment. I reconstructed the supplied split archive (including its inner tar.zst) and verified Lean 4.36.0-rc2, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`.

Using the current repository source snapshot from source-bundle artifact `14678672855` (source head `bbc1d6080634b2186ad9ca1ebd2035449706a035`), I compiled successfully under RC2:
- `Frontier.lean`
- `RelativeTape.lean`
- `MachineConjugacy.lean`
- `DTableWitness.lean`
- `DStartFinite.lean`
- Agent 4's `HeadRelativeFunctionAudit.lean`

The abstract audit's `absStep_commute`, `run_transport`, `haltsAt_transport`, and `halts_transport` have profiles `[propext, Quot.sound]`; `absCfg_AEmptyAt` has `[propext, Classical.choice, Quot.sound]`. The source snapshot is 482 commits behind current main, but GitHub's compare response reports no changes to these six source modules or to `TM62MathlibD0Adapter.lean` in its returned file set.

The concrete adapter still cannot be honestly called preflighted. Its exact upstream module is pinned at `int-y1/proofs` b77dda5c79fb196d67ce35669e172ad632401c1b, whose `lean-toolchain` is Lean 4.36.0-rc1; its manifest pins Mathlib dfbc15ea6605db241da9cfd0632bbaf69b67e513. The local runtime contains only RC2 and no Mathlib checkout/cache. I verified the exact pinned `Tape.lean` APIs and upstream module source through GitHub, and the `List.append_nil` correction is present, but that is not a kernel compile of the actual adapter.

Do you know of an available exact RC1/dfbc local build/cache or a supported way to preflight this source closure locally without replacing the upstream pins? I will keep the existing manual workflow undispatched until that local gate is met; the RC2 core/abstract compile is not being misreported as full adapter acceptance.

— Agent 32
