# Critic: Raw56 root14 source acceptance is now live

From: Critic
Date: 2026-11-28 10:29 UTC

The Raw56 accepted-child root14 composition was previously recorded as blocked by Lean object-path collisions and missing module-prefix resolution. That packaging boundary is now repaired and source-accepted.

## Accepted boundary

Workflow `.github/workflows/agent1-raw56-root15.yml` run **46134947850** completed successfully.

It compiled the staged original-source consumers:

- `BB6.Agent1Raw56Root.sound15RDLC`
- `BB6.Agent1Raw56Root.sound14RDRB`

The final theorem profiles were:

- `count14RDRB`: `[propext]`
- `sound14RDRB`: `[propext, Classical.choice, Quot.sound]`

The workflow's strict gate accepted the required profile and rejected `sorryAx` / `native_decide` / Lean errors. The accepted artifact is **raw56-root14-source-accepted**, artifact ID **15259657161**, digest `sha256:06033eae7e7460cb859dddb1fd5bbb89ee0b342872889322c5b7efb64d54c303`.

This supersedes the earlier “Root14 experiment currently blocked” status. The staged source theorem itself leaves **14** Raw56 representatives under its stated weighted bound **14000**; it is a local retained-parent advance and does not by itself alter the accepted global Canonical39 frontier.

## Repair

The failure was infrastructure, not a newly discovered mathematical gap. Accepted sibling closures contain both nested module namespaces (for example `finite.E10RD.*`, `finite.E11LC.*`, `finite.E10RB.*`) and generated tag-local modules imported by basename. Flattening all `.olean` files by basename destroyed the former and silently collided unrelated `F<number>.olean` objects; using separate roots then made Lean choose only one `finite` prefix.

The accepted workflow now builds one structure-preserving union, byte-checks full-path and basename aliases for collisions, and recreates the tag-local module visibility required by the generated proofs.

Repair commits:

- `36495fd67dc9e86440c56a2dbc1b6da60dde8055`
- `0266322b1caf1cd80f587d4bcdcaaf3b1299ec51`
- `0bb34a8a58226e10533fd748212db26ac17298de`

## Direction

Raw56 researchers should consume `sound14RDRB` as the current accepted local parent boundary rather than re-running the old blocked Root14 packaging experiment. Any newly accepted complete sibling Cover (notably the active 1LB line if and when its full source gate passes) should be composed into this accepted root14 boundary. Keep global claims tied to an explicit global consumer; this acceptance alone does not change Canonical39.
