# Raw11 Extra132 complete source-accepted Cover at weighted bound 691

## Result

The exact Raw11 Extra132 parent with table code
`27874661676483464` has a complete source-accepted Lean theorem

`BB6.Agent5Raw11Extra132.cover : Cover (WeightedBound 691) parent`.

This closes the entire Extra132 partial-machine cylinder, not merely a sampled
set of completions or a bounded simulation.

## Exact nonhalting certificate

The previously generated TwoSidedAutomata witness is preserved exactly.  Its
left and right stack automata have **2,097** and **133** states.  The twelve
state/symbol invariant rows contain

`9510, 811, 1696, 11030, 1834, 13603, 11465, 12024, 9152, 0, 5153, 7161`

states respectively, for an exact total of **83,439** abstract states.

The former source replay bottleneck was proof reduction, not certificate
discovery: a monolithic `stateStepOK` checker repeatedly unfolded the complete
stack representation and exceeded the runner memory envelope.  The replacement
uses the same exact certificate encoded by the existing bit-packed stack
representation and a new proof-oriented `SplitCheck` interface.  Each row mask
is kernel-validated independently, each finite state-index chunk is
kernel-checked with `decide +kernel`, and the generic soundness theorem consumes
those exact facts directly instead of rebuilding one giant Boolean term.

The deterministic generator
`im-results/agent44-raw11-extra28/repack_extra132.py` reconstructs the packed
certificate from the frozen transformed source, asserts the exact stack
geometry and row census above, emits proof-sized Lean modules, and changes only
the proof boundary of the original generated parent subtree.  The five
unchanged reverse dependencies then reassemble the original
`Agent5Raw11Extra132.cover`.

## Source acceptance

GitHub Actions run
[46163290235](https://github.com/FlareZ123/bb6/actions/runs/46163290235)
source-replayed the packed proof on Lean 4.36.0-rc2 from commit
`3bd974029922dba75f4cab2d8ef66551c999b8e8`.

The run compiled **92 fresh modules** in the target dependency closure and
reached the top theorem.  Its audited theorem profiles include:

- `BB6.Agent44Extra132Packed.nonhalt`:
  `[propext, Classical.choice, Quot.sound]`;
- `BB6.Agent44Extra132Packed.weighted`:
  `[propext, Classical.choice, Quot.sound]`;
- `BB6.Agent5Raw11Extra132.cover`:
  `[propext, Classical.choice, Quot.sound]`.

The audit rejects `sorryAx` and `native_decide`.  The complete-parent artifact
is **15271066058**, named `parent-complete-132-repaired`, with artifact ZIP
SHA-256
`5392f9ae5d5177ff6fb0d3fb0aa1ae325f9225ca17042ed741160038a02d9372`.

## Scope

This theorem discharges one exact Raw11 residual parent.  It does not by itself
prove a universal BB(6) upper bound.  Together with the separately accepted
Extra140 parent, it enables the exact staged Raw11 150→148 consumer without
changing any sibling cylinder.
