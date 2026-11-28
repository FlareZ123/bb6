# F197: exact blank-root self-embedding certificate

**Status:** complete reproducible computer-assisted blank-root nonhalting argument for literal table `1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF` (Raw132 named hard root). The standalone exact verifier passed locally and in [CI 46094784084](https://github.com/FlareZ123/bb6/actions/runs/46094784084). The **stronger** L^35 infinite-cylinder nonhalting theorem (where L is the 12-letter block below) was independently source-accepted in [Lean CI 46094555223](https://github.com/FlareZ123/bb6/actions/runs/46094555223). The generated blank-to-cylinder original-source `RootTheorem.blank_nonhalt` **and** original-machine `F197BlankCover.blank_cover` have now compiled successfully in [CI 46100750502](https://github.com/FlareZ123/bb6/actions/runs/46100750502) with the exported axiom gate rejecting `sorryAx`. All 25 total completions of the sole C1 hole are nonhalting from blank. Whole Raw132 and BB(6) remain unresolved. This is not a proof of the universal BB(6) upper bound.

## Reproduce

Run `python3 verify_nonhalt.py [output-directory]` (do not use -O). The verifier first checks every finite macro identity against the literal transition table on all choices of the next left/right bits; it refuses reads beyond the provided finite prefixes. It checks all fixed transport, descent, entrance, decoder, and marker identities, verifies both ordinary bulk schedules, then computes a guarded self-embedding and exact blank-root reach. Optional output contains all finite core/terminal/direct certificates, traces and bulk schedules. Local runtime 11.45 s with the full trace data emitted. A separate C++ literal simulation confirmed the blank seed.

## Configuration notation and finite-rule soundness

All strings below are nearest-first. A=10, T=1100, J=100, U=11100, C=110. At B, the inclusive left tape starts at the head and the right tape excludes it. Write B(l,r) for the physical B configuration whose inclusive left tape is l and whose right tape is 00r. Let e=1 followed by all zeros, d=11 followed by all zeros. Concatenation of a finite word with a tape is literal prefixing.

A finite prefix certificate from (B,L1,00R1) to (B,L'1,00R'1), with exact positive primitive cost, gives B(Ll,Rr) -> B(L'l,R'r) for *every* pair of tapes l,r beginning with 1. At each macro step, the finite simulator requires all bits read by that rule and applies only the known prefix substitution. The remaining opaque suffixes are never used. This is proved by induction on the finite macro trace (PrefixCheck.lean, CounterCore.lean). For a blank-right certificate the simulator supplies a stated number of known zero bits and requires the stated finite endpoint; zero padding is semantically immaterial. All 13 prefix rules are checked directly against the 6-state machine, and the locally checked Lean checker imports Agent31's exact macro proof.

## Unbounded transport and ordinary epochs

Set P=AAT, M=JTAATAAA, K=TATAAT, R=AATAAAT, L=AATAAATAUJTT; u=1111000, s=11111000, x=10, H=111100011111000110, xc=10110 (lower-case x and xc denote bit strings). The checked transport identities are

- B(P l,r) -> B(l,u 1 r), cost 36.
- B(J l,x s r) -> B(J P l,x r), cost 32.
- B(J l,x d) -> B(P l,e), cost 27.

Thus for any n>=1, B(P^n l,e) reaches B(l,u s^(n-1)d). Conversely B(J l,x s^j d) reaches B(P^(j+1) l,e). A checked local core B(Wl,u s^k r)->B(J P^a Yl,x s^j r) lifts for every n>=k+1 to B(P^n Wl,e)->B(P^(n-k+j+a)Yl,e): use the residual r=s^(n-k-1)d, then decode. Every use in the trace checks the exact source prefix and lower bound on n. All right-blank direct rules are checked separately. This is the theorem CounterCore.core.

The descent identity B(P^(n+2) M l,e)->B(P^n M K l,e) follows for n>=1 from the k=2,j=0 core of cost321 and for n=0 from the 388-step direct certificate. Hence by induction any P^(2q+p) M prefix becomes P^p M K^q. The even entry consumes M K and makes right RB0; the odd entry consumes P M and makes right RB1. Each K pushes H with cost82. A terminal certificate B(Xl,r)->B(JYl,xc r) permits arbitrary remaining H^m, since B(Jl,xc H r)->B(J R l,xc r) (68 steps). The fixed decoder exits yield P^4 E0 R^m Y for even parity and P E1 R^m Y for odd parity, where E0=AAATATATATAAAT, E1=AAATATAATAATATAAAT.

The checker verifies finite core-only schedules:
- even entrance P^4 E0 R^9 -> P^42 W0 in 76 resets, W0=AAATAATATAAATTAAAT;
- odd entrance P E1 R^3 -> P^15 W1 in 28 resets, W1=AAATATATAAATTAAAT;
- for either W, P^4 W R^4 -> P^22 W in 36 resets.

Each finite schedule remains valid for any additional leading P count by the local-core lift; an arbitrary aligned suffix remains unchanged. Iterating the last identity consumes 4R and adds18P per cycle. Therefore the ordinary epoch for n even, n=2(m+1), m=9+4q+r, yields count 42+18q and W0 R^r Y; for n odd, n=2m+1, m=3+4q+r, yields 15+18q and W1 R^r Y. In each case 0<=r<4. All exponent arithmetic is exact integer arithmetic, not floating-point or sampled extrapolation.

## Marker epoch

The marker entry and alternating pair are exact suffix-parametric identities (EpochMarker.lean):
B(TATJ l,Hr)->B(G T l,Vr) (112), B(G l,V H r)->B(G2 l,V2 r) (176), B(G2 l,V2 H r)->B(G L l,Vr) (96), where G=ATTJAUJ, G2=ACAAATAUJTT, V=1110, V2=111111000110. Thus each 2H produces one L at cost272. The four parity/residue exits (EpochMarkerExit.lean) and the K scanner (EpochEntrance.lean) compose to the following complete post-descent identities (EpochMarkerBulk.lean):
for even n use m=n/2-1, odd n use m=floor(n/2); put (k,b)=divmod(m-1,2). Starting P^n M TATJ Y, the reset result is OUT[p,b] L^k T Y, with OUT table exactly as in verify_nonhalt.py. Every right suffix consumed by the exit is the checked fixed RB buffer.

Two additional generic root epochs use independently checked guarded entry, uniform cycle, and fixed right-blank exit. Their finite certificates and exact pure-block schedule are generated and checked inside generic(). No unsupported macro extrapolation is used.

## Positive self-embedding and actual reach

Let HEAD=JTAATAAATATAATAATAATAATAATTATAATAATAATTAATTAAATAUJTT (52 letters). Start with B(P^72 HEAD L^80 l,e) for *any* l beginning in 1. The verifier constructs 3,765 exact local/ordinary-epoch rows. After 47 ordinary epochs the configuration has n=2930368004349374329 and prefix M TATJ Y, with the remaining finite word Y explicitly retained. Its odd/half marker epoch produces OUT[1,1] L^732592001087343581 T Y. The verifier then checks 256 local reset rows using only the first 90 of those L blocks. Their output is precisely P^72 HEAD L^80 L^7. Therefore for every aligned l the loop reaches B(P^72 HEAD L^80 l',e) where

l' = L^7 L^732592001087343491 T Y l.

This tape begins 1, so the positive path repeats without any finite-support or hidden suffix assumption. For every time bound N, N iterations contain at least N live primitive transitions. Hence no finite halting time exists for any configuration in the cylinder.

The verifier separately simulates exactly 5,810,803 literal transitions from blank, with no halt, to B(P^114 seedWord e,e) (inclusive left length3311, right001). It then applies the same guarded core/terminal/epoch rules and the one generic epochs, recording all finite word transformations and compressed reservoirs without expanding huge powers. Refilling a visible prefix simply repartitions the exact concatenation of finite-word powers. At epoch181, after 10,477 trace entries including refills, the state is B(P^72 HEAD L^80 l,e) with l beginning 1. This closes the computational blank-root nonhalting argument.

## Proof status and integration

**Accepted source theorem:** `F197.Agent2Self.blank_to_cylinder` and `blank_nonhalt`, followed by `F197.CoverBridge.blank_cover` at arbitrary weighted bound `B`, were compiled against the original six-state machine semantics in [monolithic root run 46094787881](https://github.com/FlareZ123/bb6/actions/runs/46094787881) and [complete four-shard build 46100750502](https://github.com/FlareZ123/bb6/actions/runs/46100750502). In the latter, base, each of four parts, and final source composition succeeded; the final job prints exported theorem axiom profiles and excludes `sorryAx`. The independent infinite-cylinder theorem was [accepted at 46094555223](https://github.com/FlareZ123/bb6/actions/runs/46094555223) with only standard axioms. `F197BlankCover.lean` universally covers all 25 possible physical C1 completions. F197 is now a **resolved named nonhalting root** and a closed weighted partial-table leaf, not a solved Raw132 parent.

**Optional shortening (not used in accepted root proof):** [root_phase_scout.py](root_phase_scout.py) located a matching source phase at root entry 10,198, earlier than the 10,477-entry cylinder entrance ([CI 46101870786](https://github.com/FlareZ123/bb6/actions/runs/46101870786)). The exploratory `PostBasin` / `GenericBasin` code would strengthen the set of live prepared states but [CI 46102524949](https://github.com/FlareZ123/bb6/actions/runs/46102524949) failed. No statement from this optional branch is used in or needed by the already accepted F197 blank Cover.

**Remaining BB(6) quantifier:** the complete Raw132 parent complement and 39 other retained Canonical40 parents must still be bounded at the champion score. The independent F321 table is not a completion of F197 and is not decided here.
