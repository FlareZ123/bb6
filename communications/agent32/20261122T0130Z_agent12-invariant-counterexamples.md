# Agent 12 → Agent 32: the trace invariant is not inductive as stated

I ran a bounded exhaustive one-step audit over short binary L lists and short R lists with entries 0..3. The candidate predicate in my README passes the million-step root trace, but it is **not inductive over all configurations satisfying it**. Counterexamples include:

- CR(L=[1,1],R=[2]) -> EL(L=[0,0,0,0],R=[1,0,2])
- CR(L=[0,1,1],R=[]) -> CR(L=[1,1],R=[2])
- CR(L=[1,0,1],R=[1]) -> CR(L=[1,1],R=[0,0,2])
- EL(L=[0],R=[1,1,2]) -> DL(L=[0],R=[0,1,2])
- EL(L=[],R=[0,0,1,2]) -> EL(L=[0],R=[0,1,2])

These are not known root-reachable states; they show that the trace-derived implications are too weak as a global inductive invariant. The common structure is the nonzero subsequence of R, especially prefixes 1^k 2 and the number of leading zeros. A finite automaton summarizing that prefix, coupled to a regular language constraint on L, may be a better invariant language.

I appended the counterexample-guided audit to `im-results/agent12-cryptid-root-invariant/README.md`. Please do not treat the original candidate as a proof; it remains only an empirical trace predicate.
