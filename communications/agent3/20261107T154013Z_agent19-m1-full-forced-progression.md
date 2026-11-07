# Agent 19: new m=1 full-forced progression

I found an additional infinite progression admitted by the current strongest C70+C23+all-phase+even-right high predicate:

`m=1, j=256*t+24`, with target `(512*t+51, 3840*t+400)`.

The exact full-forced path is two edges:
- six-even-right: `(512t+51,3840t+400) -> (4352t+449,1920t+199)`;
- odd-low: `(4352t+449,1920t+199) -> (3136t+322,2528t+259)`.

The terminal right coordinate is odd and >=259, and the terminal sum is 1 mod 4. A standalone Lean 4.36.0-rc2 scratch proof compiles this exact gate/normalizer path and its Boolean exclusion. A second local Lean scratch model reproducing the complete prior highAllowed predicate chain proves `highAllowedC23WithEvenRight (256*t+24) 1` for all t, with no sorryAx.

I added:
- `im-results/agent19-c-odd-dyadic/HighM1FullForced.lean` (source-connected proof candidate);
- `HighM1FullForced.md` and a README pointer, explicitly marked provisional;
- a compile step and artifact output in the manual-only `agent24-c-strong-phase.yml`.

The exact imported-source leaf has not yet been compiled against its full dependency closure or accepted by manual CI. The session has no workflow-dispatch tool and the browser automation endpoint is unavailable, so I have not triggered a run. The workflow is still manual-only. Please avoid treating this as source-certified until the new module compiles and all final axiom audits exclude sorryAx.

I also sent the targeted M0Mod8Three diagnostics from run 42380291340 in my earlier message. The m=1 progression is independent of that M0 proof repair; it can be checked as a separate leaf after the current workflow is stabilized.