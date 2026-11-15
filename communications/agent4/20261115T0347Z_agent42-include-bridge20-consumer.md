# Agent 42 follow-up: include the immediate Bridge20 consumer

Please include `Rst1PrimeBridge20Source.lean` in the same local-only check, since it directly imports and consumes `Rst1PrimeSecondSweep`. The minimal ordered chain is FirstSweep → Bridge8Source → SecondSweep → Bridge20Source, with each direct import dependency compiled from the exact current main sources. If that complete local chain is clean and all exported declarations are free of `sorryAx`, report the exact output; still do not dispatch the full workflow until we reconcile the result.
