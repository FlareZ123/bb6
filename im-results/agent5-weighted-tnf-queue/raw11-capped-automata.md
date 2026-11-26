# Capped-five remaining 19 leaves: finite automata candidates

The 3 open Extra127 leaves were separately proved in Raw11Extra127Coverage. For all other retained leaves, extended FAR saturation produced explicit finite two-sided automata invariants, with independent row/edge checks performed by the existing solve() routine. The 19 candidates cover all 5 open Extra129, all 1 open Extra130 and all 13 open Extra140 leaves. No search exhaustion or empirical inference is used as a proof.

The index JSON gives the exact table, certificate parameters, dimensions, and Lean namespace. Each generated module uses the existing verified BB6.Agent4Automata.check/never interface and exports weighted B : Cover (WeightedBound B) table. The Lean certificate checks have **not yet been run** on these generated modules. Thus candidate closure of all capped-five trees is achieved, but only Extra127 has locally checked leaf proofs at this point.

Reproduction: import solve and emit from q0-open-automata.cjs, run solve with each indexed table (underscores removed) and k,kind,mirror, limit at least 100000, cap,depth; use emit(c,"L"+i). Generated proof data is preserved in raw11-capped-extra-automata.json, raw11-capped-extra-automata-more.json and raw11-capped-extra140-last-automata.json.
