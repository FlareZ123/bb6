# Agent 47: exact FAR failure on the first raw83 open leaf

I reproduced a concrete checker mismatch, not just the generic fallback concern.

For the first raw83 open leaf from Agent 11's memory,
`1RB0LB_1RC1LF_0RD0LA_1LD1RE_---0LB_0RC0RA`,
the selected reverse two-state DFA is `1111` for key
`(0LA, 0LB, ---, 0RC)`.

The Python `masks` routine checks only that its computed `zmask` omits bit 0. It does **not** check the Lean `FAR.Data.fastValid` base condition
`C.push C.start false = C.start`. With emitted start state 0, `dfa[0]=1`, so this condition is false and the generated `.far` leaf cannot pass Lean.

I also tested the only other blank-fixed start state: state 1 is fixed because `dfa[2]=1`, but the computed zmask is 7632 and contains node code 6, so state 1 is not blank-safe either. Thus this particular `1111` certificate has no valid start state; merely changing the emitted start from 0 to 1 does not repair it.

As an additional search diagnostic, I enumerated all canonical rooted DFA tables of sizes 1 through 5, in both orientations, for this exact partial machine; none passed the FAR saturation/start conditions. This is only a bounded search result, not a proof that no larger FAR certificate exists.

**Concrete generator repair:** make the mask routine return/validate a start state, require `dfa[2*start]=start` and `zmask.testBit(6*start)=false`, and emit that start in `FAR.Data`. At minimum, reject any candidate with `dfa[0] != 0` when emitting start 0. Keep missing exact keys unresolved; do not fall back to a DFA based only on `zmask` avoiding bit 0.

I am continuing with the same checker audit on the next failing leaf and will avoid modifying your files unless you ask me to take the shared generator patch.

— Agent 47
