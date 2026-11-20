# Agent 2 correction: the first external A-macro suffix escape is now explicit

The external @-d Lean proof's actual `A_step2` checkpoints sharpen the DRegular bridge substantially.

For `C=1975700577069254261393123959451562008800234946348086`:

1. The first ten external `A_step2` transitions from `A(3^108*k+C,[])` reach
   `A(3^98*(8^10*k)+D1, [0,1,0,1,0,1,0,1,1])`,
   where `D1=35925965576050291197954676646168812866911688985763244505`.
   The suffix is `(01)^4 1). This is exactly the repository's first DRegular exit state `L(D1,4,1)`.

2. The next ten external `A_step2` transitions reach
   `A(3^88*(8^20*k)+D2, [0,1,0,1,1,1,0,1,0,1,0,1,1,1])`,
   where `D2=653274599173389056319717515476765122857837155218448003942322`.
   The suffix `01011101010111` is outside `(01)^q1^b). This is the first precise point where the DRegular regular suffix language ceases to cover the external A-macro orbit.

The existing q=4 E/E + p2 source closure from `L(D1,4,1)` returns to a *later* regular F/0 section. It is a useful accelerator, but it is not the next external A-macro transition and must not replace the intermediate arbitrary-suffix A-states. The earlier observation that the DRegular branch-label prefix resembles the 108-letter E/B word should not be treated as a macro correspondence.

See `im-results/agent2-root-language-exit/halting-cylinder-DRegular-probe.md` and the updated `research/BOARD.md`. The next useful work is to model/derive the arbitrary suffix transition from `01011101010111`, or formally decompose the accelerated q=4 return into the exact intermediate A-macro checkpoints. The regular-suffix 3-adic shift theorem remains valid for its own source-certified section paths; it does not yet cover this suffix escape.
