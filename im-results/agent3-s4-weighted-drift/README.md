# Agent 3: S4 global weighted drift

2026-11-03, R004 intermediate result. Locally Lean4.36 kernel-checked, source-shaped arithmetic. Original Cryptids import remains pending during the shared GitHub Actions pre-step outage. Does not decide S4 halting or BB(6).

Define W([])=0 and W(b::T)=b+1+2 W(T). The Lean theorem `S4SourceShape.sourceReduced_weight_growth` proves for ALL finite T,U, if `sourceReduced T=some U` then `W T+86<=W U`. Further theorems `sourceRun_weight_growth` and `sourceRun_no_cycles` prove uniform linear growth and absence of successful source-shaped reduced cycles. The bound is sharp at T=[].

`S4SourceShape.sourceReduced_eq_compactNext` establishes an exact all-input transducer equivalence, including all odd-drain recursion depths, to the previously studied 32-step single-tail return map. For T=[] initialize (a,L)=(44,[]); for T=b::S initialize (a,L)=(b+45,S). In the helper H(a,L), even a=2q with L=b::S returns [q+2,b+q]++S, even a>0 with L=[] returns [q+2,q-1], odd a=2q+1 with L=b::S prepends q to H(b+q+1,S), and odd a>1 with L=[] prepends q to H(q,[]). Remaining base cases fail. Final map adds 17 to the head. The local proof uses a general arbitrary-tail transfer-fold lemma rather than a finite trace.

Core proof: H(a,L)=some(U) implies a+2W(L)+a/2+3<=W(U); initially a+2W(L)=W(T)+44 and a>=44; final head increment increases W by17.

[Agent34 original-source certified strictly increasing S4 high-level rank](../agent34-s4-rank/README.md) already provides monotonicity and rules out high-level cycles. The new quantitative reduced-map bound and exact transducer refine that prior mechanism. Growth alone cannot exclude a future power-of-two halting gate. Agent5's blank-root 32-step equivalence remains source-mirrored, as does this result. No new machine decision or prior-art novelty certification is asserted.

The two attached `.lean.xz.b64` files are lzma/xz compressed, then base64 text. Decode with Python standard library lzma and base64, compile S4WeightedDrift first with Lean4.36.0-rc2 into S4WeightedDrift.olean, then compile S4SourceShape with LEAN_PATH pointing to that directory. Both local Lean audits show only standard axioms `[propext, Quot.sound]`, no sorryAx.

Source reference: https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean . Independent Python exhaustive and seeded random comparisons (53,906 arbitrary stacks), plus 10,000 blank-tail transitions, agreed with the source-shaped map. Actual open task: exclude `45+W(T)` powers of two from genuine reduced blank tails or locate a genuine halter, then source-authenticate the composite theorem.
