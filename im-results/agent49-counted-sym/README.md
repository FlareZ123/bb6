# Shared counted symbolic semantics (draft)

The 19-field `CountedAtoms M flag` interface is the exact-count analogue of the actual upstream `HasSymRunRules M` interface. It separates the original concrete-machine primitive witnesses from the shared symbolic BB/DL/CB semantics. `flag = false` selects F412 costs, `flag = true` F424 costs. No state labels of either concrete machine appear in the generic proofs.

`CountedSymPure.lean` lifts the original-source atomic witnesses to exact `stepPure` and `costIter` reachability for an arbitrary machine satisfying the interface. Proof structure is adapted from Agent26's F412 draft and the original HaltShared source. The exact counted class avoids maintaining two nearly identical semantic proofs. The two actual original-machine instances remain to be constructed from the extracted primitive witnesses.

Status: new proof draft, not accepted. Do not treat it as a halting-time theorem or a BB(6) bound. The current F412 audit (45426229265) will inform corrections before generic integration. All source imports are literal pinned Cryptids `3647718b5df22e1a61462dec0376bd204526285a` and Agent11's shared `SourceCostModel.lean`.
