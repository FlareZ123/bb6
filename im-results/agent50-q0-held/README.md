# q0 held machine: exact B-return reduction and inverse-refined pushdown abstraction

Table: `1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA`. E1 is the only hole. **No halting decision is established.**

At B, L lists cells strictly left of the head, nearest first; R lists the current cell and cells to its right. Both have infinite zero tails. A0 from blank gives L=1000..., R=0000.... Write L=lp·X and R=rp·Y. Each row replaces L by reverse(lw)·X and R by rw·Y and returns to B.

| lp | lw (bottom to top) | rp | rw | Live moves |
|---|---|---|---|---:|
| ε | ε | 00 | 11 | 6 |
| ε | 101 | 0100 | 0 | 5 |
| ε | 10011 | 01010 | ε | 5 |
| ε | 1001 | 010110 | 11 | 8 |
| ε | 1001 | 010111 | 11 | 6 |
| 00 | 1 | 1 | 10 | 3 |
| 01 | ε | 1 | 110 | 4 |
| 10 | ε | 1 | 010 | 2 |
| 11 | ε | 1 | 110 | 2 |

The remaining case R=011·Y reaches E1 after two live moves. This partition is exhaustive and disjoint, verified by symbolic branching at each previously unread cell until the first B return or E1 query. The exact machine decision is therefore whether the blank B orbit ever has right prefix 011.

## Counterexample-guided abstraction

Abstract L by a bottom-to-top push DFA with zero-loop blank state 0. Keep R exact using a pushdown system with bottom marker Z for the infinite zero tail. Each macro takes all abstract left-state changes induced by any possible predecessor state after its left pop. Normalize right rewrites into single-pop rules; zero pops on Z preserve Z. Backward P-automaton saturation decides reachability of the fatal language in this abstraction.

When the abstract initial configuration reaches the fatal language, extract its derivation and replay the concrete left stack. At the first spurious inverse pop, refine the DFA using a predicate for the exact popped suffix and the chosen predecessor state. Minimized Moore products preserve prior distinctions. Every refinement is a sound overapproximation, but termination is not proved. A safe result would require an independent closure audit.

Run `python held_cegar.py --rounds 42 --seconds 120 --output run.json` or resume with `python held_cegar.py --resume checkpoint-83.json --seconds 30 --output resumed.json`. The experimental run reached 83 states after 42 refinements; the final refinement used a 228-macro counterexample and 44,430 saturation edges. No safety decision. Separate primitive simulation reached 100 million live moves without halt, which is only bounded evidence. Existing periodic/run automata and experimental numeric/length/popcount modular abstractions yielded no certificate. The code here is a compact transcription of the tested prototype.
