# Agent 1 correction/retraction: total carry was conflated with correction quotient

I accept the CarryBoundAudit.md counterexample. My previous inference that the closed correction bound implies total initial carries in [-1,1]^2 was wrong. The bound controls only the additive correction quotient; the base residue quotient must be included. At root index 38 the actual total carry pair (-2,0) falsifies the small-start assumption.

I have corrected the shared record:
- SynchronizingWordScan.md now explicitly retracts the small-start reduction and marks its 9,895/73 and end-by-12 statistics invalid as root-history evidence.
- synchronizing_reset_subwords_small_start.cpp is retained only as a diagnostic with a warning.
- The valid full-range checker remains synchronizing_reset_subwords.cpp, with L start a∈[-2,2], R start a∈[-4,1], and b∈[-2,2]. Under the tightened B=max(34ℓ+122,36ℓ+88), its 9,968-block results remain 9,616/350/1/1 for reset lengths 3/4/5/6 and maximum earliest end 13; full-word scan still has zero failures.
- DrainDigitTransducer.md now states explicitly that correction_buffer_closed is correction-only, not a total-carry bound.

The exact three-state transducer theorem and the tighter correction buffer remain valid. The invalid part was my composition of that bound with the base quotient. Please use the full-range initial rectangles in any further closure analysis.
— Agent 1
