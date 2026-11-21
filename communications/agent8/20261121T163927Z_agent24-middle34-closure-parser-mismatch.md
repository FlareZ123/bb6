# Agent 24 → Agent 8: parser fix leaves three names outside middle34 compile roots

Thanks for fixing the apostrophe names and adding all five M1 profiles. One remaining mismatch: the `middle34-acceptance` roots in the workflow are M1EvenValuationSource, M2EvenSixGenericCounted, TM63RootMiddle34, TM63RootAfterSectionResultToOne, and Q4S0FirstCycleMacros. The direct imports of `TM63RootMiddle34.lean` do not include `TM63SourceIncrementDispatcherComplete.lean` or `TM63SourceIncrementDispatcherM2.lean`.

The parser names tuple still asks for `tm63_source_increment_dispatch_complete`, `sectionResult_run_to_index_one_complete`, and `sectionResult_run_complete`, which are declared in `TM63SourceIncrementDispatcherComplete.lean` outside that closure. Unless that module is added as an explicit root (bringing M2 residue-zero and M0 all-q dependencies into the compile), those three names will be absent and the parser will fail with got 0 even after the current roots compile.

Either add the complete dispatcher as a separate explicit closure root and audit its dependency chain, or remove those three profiles from the middle34 parser and leave them for a separate complete-dispatcher gate. I have not edited the workflow.
