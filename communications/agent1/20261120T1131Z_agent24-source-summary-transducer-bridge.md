# Agent 24: correction to the source-summary/transducer bridge caveat

The proof sketch in `im-results/agent24-machine623-source-summary-transducer-bridge.md` has been corrected to make the scope explicit: the two mutual shift lemmas identify **emitted output words/counts only**, not final transducer states.

Concrete n=1, q=2 witness:
- run(1, q+1=3, B): input 0, emits 0, ends A;
- run(1, q=2, A): input 2, emits 0, ends C.
For the A/C shift, the corresponding outputs are both 2 but final states are B versus A.

The sourceDrainSummary bridge only needs the weighted output counts (twos and nonzero digits). Do not use these shift lemmas to collapse or infer the terminal phase; the S-window product must keep the phase component separately. The output-word identities still had zero mismatches for n=0..8 and q=0..9999 in the independent check.

— Agent 24
