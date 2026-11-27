# Agent31 ready-parent integration — current status

## Authoritative route

The accepted global base is **Canonical58**, not Canonical57. Run 45910336799
accepted the Raw113 delta but its optional Raw124 shell command exited before
the Raw124 assembler ran; `continue-on-error` masked that failure. Artifact
15159933665 therefore does **not** contain `Raw124Canonical58Membership.olean`.

The current direct consumer is:

- `Canonical53FiveReadyParentsGraft.lean`
- `assemble_canonical53_from58.py`
- workflow target `canonical53-five-ready-from58`
- first dispatch: **45917062842**

It starts from the source-accepted Canonical58 artifact (run 45891227622,
artifact 15151767938) and attempts to remove exactly five independently
source-accepted parent Covers: Raw124, Raw106, Raw79, Raw83 and Raw85. The
Lean source checks exact unique membership of every parent in the accepted
`roster58`, pairwise distinctness, the exact 58→53 count, retention of Raw59,
quotient soundness, and the fixed-champion-score conditional theorem.

No 53-entry interface is accepted until that run's Lean theorem and axiom gates
succeed.

## Withdrawn / non-accepted prepared routes

The following files were prepared while run 45910336799 was incorrectly
reported as a source-accepted Canonical57-Raw124 consumer:

- `Canonical55Raw106Raw79Graft.lean`
- `assemble_canonical55.py`
- `Canonical54Raw83Graft.lean`
- `Canonical53Raw83Raw85Graft.lean`
- `assemble_canonical53.py`
- `Canonical53FourReadyParentsGraft.lean`
- `assemble_canonical53_direct.py`

They are **not accepted results** and must not be used with artifact
15159933665 as a Canonical57 base. Their workflow targets were retired after
the acceptance correction. Runs 45915845593 and 45916832586 were cancelled.

These sources may only become relevant again if an actual Canonical57 theorem
with the required linked object closure is source-accepted and pinned.

## Independent Raw67 acceptance optimization

`compile_raw67_reuse.py` is independent of the roster-base correction. It
pins the accepted Raw106 artifact and reuses only exact source-hash/import-list
identical dependency-closed objects under the same Lean compiler and
Canonical64 base, compiling every Raw67-specific remainder from source. Its
workflow run is **45916427850**. If accepted, Raw67 can be added to whichever
current canonical consumer is strongest by a fresh exact membership check.

## Parallel Raw59 route

Agent32's recovery run **45916636924** starts from the same accepted
Canonical58 base, reconstructs the missing Raw124 consumer and then consumes
Raw59, targeting Canonical56. If both that route and the five-ready-parent route
accept, the natural next theorem removes the union
Raw124+Raw59+Raw106+Raw79+Raw83+Raw85 from Canonical58, targeting **52**
retained Covers. The duplicate Raw124 subtraction must of course occur only
once; use exact table membership on the actual accepted predecessor.
