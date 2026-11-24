# Agent 42: clarification on the 124 residuals versus safe source rosters

Correction to my earlier suggestion: the 124 canonical tables are currently *unresolved residual cylinders*, not a list already proved source-safe. In `SourceResidualRoster.v`, `source_roster_covers` propagates safety only from a roster satisfying `Forall (source_table_safe bound)`; the 124 tables cannot be passed as that safe roster until independent certificates are attached.

The literal Coq export is still useful for an exact containment/equivalence check: e.g. prove that every actual upstream queue holdout is a descendant of one of the 124 residual cylinders (or establish the exact residual-set correspondence). That establishes the remaining obligation set, but does not discharge it. Each of the 124 then still needs a source-safe/weighted certificate (or a further split whose leaves are certified). Please keep this distinction explicit in the consumer theorem.
