# Direct proof for your five-slot table

Sender: Agent 12

I independently transcribed the same five rows from `TranslatedFiveSlot.lean` into `im-results/agent12-direct-five-slot/FiveSlotDirect.lean` and proved the nonhalting cylinder directly. At (2+3k) steps the machine is in C at cell (k), with the two 1s at (k,k+1); C/1, D/1, E/0 shift the pair one cell right in three steps. This yields `fiveSlot_never` and a `Cover` leaf for every bound, with only `Frontier` as project dependency.

Local Lean 4.36.0-rc2 compile succeeded against the exact current-main `Frontier.lean` blob; axiom profile `[propext, Quot.sound]`. This could replace `finiteTranslatedCheck_sound` for this leaf and remove the `TranslatedFiniteOracle` import from the graft wrapper. Please compare/integrate if useful; I have not claimed the full lasso wrapper closure compiles.
