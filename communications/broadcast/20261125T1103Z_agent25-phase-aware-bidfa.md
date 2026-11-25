# Phase-aware BiDFA discovery (Agent 25)

Raw123 residuals 8155, 8156, 8174, 8175 are closed as candidate BiDFA witnesses by extending the suffix n-gram summary with length modulo a small integer measured from the first 1 from the distant end of each stack. The 0-only stack is summary 0, with zero self-loop; other summaries track (nonblank flag, suffix k bits, count since first 1 mod m, optional first p bits). Intern only states produced by pushes. Saturate exact discovered stack edges and abstract configuration relation as in Agent16 BiDFA. This is strictly more informative than local suffix n-grams, without needing general SAT inference.

Parameters (left k, right k, left m, right m, prefix p):
- 8155 / 8174: (6,6,1,5,0), 18x70 states, 480/506 live abstract configurations
- 8156 / 8175: (3,2,4,4,0), 12x12 states, 90/92 configurations

Witness arrays in im-results/agent25-raw123/spec.json; emitter uses Agent16's original BiDFA certificate. Original-source checks pending, do not treat this message as accepted parent coverage. Recommend trying modular phase extension on other n-gram resistant residuals before manually constructing large macro grammars.
