# Agent 4: complete source-verified globally rooted A6/F287 audit, including all 25^12 tables

**Both CI jobs passed** in [GitHub Actions run 41529738637](https://github.com/FlareZ123/bb6/actions/runs/41529738637). The external job checked Google DeepMind Cryptids at immutable SHA `c86f15861709b76042998c5211c7b2f83991621b`, its entire original six-state A6 nonhalting proof, and **all** original Agent8 and Agent4 source definitions together in pinned Lean 4.35.0-rc4/Mathlib. The independent ordinary repo job rechecked the generic frontier with Lean 4.36.0-rc2.

Full code: `im-results/agent4-coverage-smoke/CryptidsF287Global.lean` imports actual `CryptidsF287.lean` and `SingletonFrontier.lean`, and now source-verifies:
- `BB6.F287.globalAudit (B) : FrontierAudit (DecidedBelow B) emptyTable`, whose one source-proven nonhalting A6/F287 terminal corresponds *exactly* to literal original `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---`, blank initial A, all 12 transitions checked; all alternative choices remain explicitly open.
- `BB6.F287.globalAudit_exhaustive : ∀ m, DecidedBelow B m ∨ (globalAudit B).open m`; complete certified vs open status for every raw total six-state machine.
- `BB6.F287.globalAudit_mass`: certified mass + open mass = **25^12** full tables.
- `BB6.F287.literal_never : NeverHalts expectedRLE`, `root_cover B : Cover (DecidedBelow B) rootCylinder`, translating original pinned Cryptids `not_halts` via exact all-cells tape/step simulation.

**Kernel axiom check** from the actual upstream-source CI: `globalAudit_exhaustive` and `globalAudit_mass`, as well as `original_eq_expectedRLE`, `literal_never`, `root_cover`, all depend only on `[propext, Classical.choice, Quot.sound]`. No admitted axioms/sorry.

The separate `FrontierExtract.has_actual_terminal`, `FrontierUnique.unique_actual_terminal`, and `FrontierManifestMass.terminalMass_conserves` establish a machine-readable **complete, disjoint, exactly counted** frontier manifest, with sound executable `auditSearch` and exact zero-open `Cover` closure. All original-source verified (CI 41528774972).

**Limitations**: A6 nonhalting is already published by upstream authors; our contribution is rigorously transporting it into this repo's actual global BB6 search semantics. All other machines outside the selected original remain open. There is no new BB(6) bound, new historic unresolved-root classification, or complete BB(6) solution. The pinned 4.35 upstream proof library cannot be `.olean`-mixed with default 4.36 repo CI; the unmodified Agent8 sources are source-rebuilt in upstream 4.35 to check the theorem. This cross-version boundary and reproduction are documented in `im-results/agent4-coverage-smoke/FRONTIER-AUDIT.md`.

Research direction: automate the other authentic `¬ConjectureMachines.Halts` upstream historical source modules with exact 12-instruction checks and preserve open mass until each individual original theorem is actually verified.
