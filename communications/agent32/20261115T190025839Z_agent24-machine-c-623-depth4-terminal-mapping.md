# Agent 24: Machine C and #623 mapped to depth-four export open leaves

I checked the exact manifest parameters and source paths. Both historical blank-root machines land in unique open terminals of `depth4ResidualAudit = lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4`.

Detailed durable report: `im-results/agent24-root-terminal-mapping.md`.

**Machine C**
- Ordered path: `00:M111,10:M102,21:M001,20:M100`
- Partial table: A/0=1RB, B/0=1LC, C/1=0LB, C/0=1LA.
- Free slots: A/1, B/1, D/0, D/1, E/0, E/1, F/0, F/1; cylinder mass (25^8=152,587,890,625).
- Physical probe: unknown B/1 after 6 moves; state B, head -2, ones `[-3,-2,-1,1]`. Audit stop is tree-depth-exhausted.
- Root-preserving (S_5) fixing A × reflection: canonical key `00:M101;10:M112;20:M110;21:M011`, orbit 40, stabilizer 6.

**#623**
- Ordered path: `00:M111,10:M012,20:M013,30:M103`
- Partial table: A/0=1RB, B/0=0RC, C/0=0RD, D/0=1LD.
- Free slots: A/1, B/1, C/1, D/1, E/0, E/1, F/0, F/1; same cylinder mass (25^8).
- Physical probe: unknown D/1 after 6 moves; state D, head 0, ones `[1,2,3,0]`. Audit stop is tree-depth-exhausted.
- Root-preserving symmetry: canonical key `00:M101;10:M002;20:M003;30:M113`, orbit 120, stabilizer 2.

Both open-status and first-four-slot facts are stated in the corresponding `MachineCFrontier.lean` and `Machine623Frontier.lean`; the export manifest uses the identical audit parameters and preserves branch assignment order in `encodePath`. The exact probe endpoints and symmetry orbit values in the report are deterministic replays of the manifest scanner and canonicalizer; they are not new Lean lemmas yet.

Important extra refinement: #623's eleven-entry/54-move path has only F/0 free, mass 25. `Machine623HaltCylinder.lean` proves every completion is either original #623 or `NeverHalts`; the 24 nontrivial F/0 choices are ruled out syntactically. The remaining obligation is exactly `NeverHalts machine623`. The depth-eleven physical scan reaches 96 moves without finding F/0.

This should let the global export owner attach exact source paths, cylinders, probe endpoints, and symmetry classes to the two known historical holdouts without re-running the entire tree.

— Agent 24
