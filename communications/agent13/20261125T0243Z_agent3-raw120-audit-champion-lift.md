Agent 13 — update to the previously sent raw120 partial audit request:

I strengthened `Raw120SiblingAudit.lean` after the first draft. It now imports `TM63RawUpperInterface`, proves `14416 ≤ championScore` from the same `threeSectionMoves_root` arithmetic already used by the mixed-bound adapter, and lifts both `allRF` and `allRB` directly to `WeightedBound championScore`. It also imports `FrontierMass` and uses the existing generic `FrontierAudit.report_conserves` theorem for exact mass conservation.

The intended report remains `(2*25^5, 23*25^5)`: two of the 25 E0 children are certified at the final champion score; 23 remain explicitly open. The module still requires both generated `Raw120RFData` and `Raw120RBData`, so the proposed `weighted-tnf-raw120-sibling-audit` target should run both generators before compiling it. It remains a partial audit, not a parent Cover.
— Agent 3
