# Reset-language nonclosure under the raw branch transducers

**Status:** exact finite counterexamples. This falsifies the tempting invariant “every word containing a common reset pattern maps to another such word” when the input word is otherwise unconstrained. It does not contradict the authentic-root scan, whose digit words have additional arithmetic and boundary-phase constraints.

The 263-state DFA in `ResetPatternDFA.json` recognizes words containing a common reset pattern of length 3--6. The shortest raw-transducer counterexamples already have length 3.

## L branch

Take the full-range L start state
[
(x_{-1},y_{-1},a,b)=(0,0,-2,-2)
]
and input digit-pair word
[
W_L=(00,02,00).
]
This is itself a common reset pattern, so the reset DFA accepts it. Under the L transducer
[
r_x=x_i-y_{i-1}+a_i,qquad r_y=y_{i-1}+b_i,
]
the output word is
[
U_L=(11,02,10).
]
The reset DFA rejects (U_L): it contains no common reset pattern.

## R branch

Take the full-range R start state
[
(x_{-1},y_{-1},a,b)=(0,0,-4,-2)
]
and input word
[
W_R=(00,01,00).
]
This is a common reset pattern. Under
[
r_x=-x_i-x_{i-1}-y_{i-1}+a_i,qquad
r_y=x_{i-1}+y_{i-1}+b_i,
]
the output is
[
U_R=(21,12,10),
]
which the reset DFA rejects.

## Consequence

The reset-pattern language is a useful finite recognizer, but it is **not invariant under either raw transducer**. A #623 proof must retain the root-specific phase: the actual boundary carry, sector/sign branch, moving-window offsets, and the arithmetic restrictions on the authentic digit-pair words. Do not infer closure merely from the fact that the current word contains a common reset pattern.

The existing root index-33 suffix counterexample remains a separate regression case. These length-3 witnesses are simpler raw-language counterexamples, not substitutes for that root-specific witness.
