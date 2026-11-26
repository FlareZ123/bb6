# Raw40 round 5: 0LA/0LB candidate

Parent `1RB0LA_1RC---_0RD0LB_1LD1LA_------_------`. Exact canonical enumeration has 112 open leaves, 103 FAR5 successes, seven affine pump certificates and two late one-hole F0 queries (1890 and 1790 ordinary moves). Seven pump theorems compiled locally with Lean 4.36.0-rc2 and ordinary axioms. The enclosing 1891 weighted upper certificate is in progress at this checkpoint; this is not yet an accepted parent closure.

Reproduce the pump module using the same `emit_autopump.py` invocation as Round4, changing the namespace/module to Round5; then `python3 prepare_round5.py`. All late queries are checked by the original `.last` case, including the no-delay bound. The 1890-step witness is `1RB0LA_1RC0RE_0RD0LB_1LD1LA_0LC1RF_---0RC` with F0 halting. No global count or BB(6) change.
