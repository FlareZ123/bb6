# Arbitrarily interleaved four-token reset transducer

This strengthens Agent2's accepted P/Q-before-paired-data theorem by removing the ordering restriction, and strengthens JCarry's TTJ family.

Use run letters A=10, T=1100, J=100, P=AAT, Q=TAT, u=1111000, τ=111000, C=110, e=1, d=11 terminal. Set x=A, inc(R)=1R. Tokens are any sequence of AT, TT, P, Q, with terminal AAA or TAA and an arbitrary run-aligned left suffix X. Each token has flag 0 for AT/P, 1 for TT/Q; terminal flag is 0 for AAA, 1 for TAA. H(0)=AT, H(1)=P.

For a list of m tokens and terminal flag v, let f be the first token flag or v if empty. The exact return is

    B(W terminal X,e) -> B(A H(f) E1 ... Em X,e)

where E_i depends on its token and the flag of the following token (or terminal):
* AT/TT: emit H(next flag).
* P/Q: emit P if next flag=0, AP if next flag=1.

If t is the count of true flags among the tokens and terminal, the exact cost is 74+68m+14t. Prefix length increases by 2: each emitted token width differs from its input width by 2(next flag - own flag), so the widths telescope; the terminal and base output supply the remaining +2.

## Stronger compositional middle theorem

For arbitrary right continuation R whose first bit is 1, scanner token pushes on the right are τR, τAR, u inc(R), uCR respectively, costs 8,18,36,46. At terminal flag v, the machine reaches J on the left and x D_v(R) on the right in 47+10v steps, D_0=inc, D_1=C-prefix. One exact reverse peel restores x D_own(R) and inserts E_i after J, costing 60+4next for AT/TT and 32+4next for P/Q.

F197.MixedCarry.sandwich proves the arbitrary-list statement uniformly for arbitrary aligned R. This single induction removes the previous need for separate adjacent-token case lists or a specific oldest base marker. Base decoding at R=e costs 27+4f. All equations are direct primitive-run equalities; no bounded simulation hypothesis. The TTJ insertion lemma additionally gives a return whenever T Y parses as the four-token family: B(TTJ Y,e) -> B(T P H(f) E1...Em X,e), cost 209+68m+14t, exactly +5 bits.

Local Lean 4.36.0-rc2 checked MixedCarry.lean and JCarry.lean using a literal-definition and run-add/decomposition slice of the existing Macro.lean. The local axiom profiles of sandwich, family, and familyJ are [propext, Quot.sound]; individual core equalities depend only on Quot.sound. Full original repository import/CI is still unverified.

## Scope

In a 5000-reset sample from the standard d/e reset, 4215 resets matched the mixed family and nine matched TTJ-mixed. Every predicted bitword and cost matched the exact macro interpreter. This is sanity evidence, not a proof of coverage on the blank orbit. The remaining 776 cases include 682 occurrences of the known P^n JTAATAAA... descent, plus other marker interactions and near-terminal tails. The universal closed grammar remains open; F197 is not certified nonhalting and no global BB(6) frontier reduction follows.
