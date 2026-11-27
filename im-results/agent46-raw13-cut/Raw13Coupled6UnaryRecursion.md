# Raw13 recursive unary five-cell transfer

Literal partial machine `1RB1LD1RC0RB1LA1RE1LF0LA1LC1RA1LE---` (F1 unassigned). Let Z=00000, U=11111, H=10000, S=0101011. Configurations use the repository's head-inclusive nearest-first left word. A(l,r) is state A; B^+(l,w) is state B with current head as the first cell of w and l the exclusive left word.

The finite identities, for arbitrary protected L,W where indicated, are:

- A(0L,W) -> B^+(1L,W) in 1 step.
- B^+(L,UW) -> B^+(ZL,W) in 5 steps.
- B^+(L,S) -> A(L,S) in 9 steps.
- A(HL,W) -> A(L,UW) in 5 steps.
- A(1,W), with the rest of the left tape blank, -> A(empty,UW) in 5 steps.

The first three imply setup A(0L,U^k S) -> A(Z^k 1L,S) in 5k+10 steps. Define T(k) by the exact recursive transfer A(Z^k L,S) -> A(L,U^k S). For k=0 the cost is zero. For k+1, apply T(k) to the first k blocks; this leaves A(ZL,U^k S). Apply setup to obtain A(Z^k H L,S). Apply T(k) again to obtain A(HL,U^k S). The 5-step pop gives A(L,U^(k+1) S). Therefore

T(k+1)=2T(k)+5k+15, T(0)=0, so T(k)=20(2^k-1)-5k.

The blank-start seed reaches root(0)=A(empty,S) at step 18. For root(k)=A(empty,U^k S), use blank-left setup, T(k) with tail 1, and the final 5-step blank pop. Exact cost is 5k+10+T(k)+5 = 20·2^k-5. Thus the root time is 20·2^k-5k-2. This is an all-width nonhalting argument for every compatible completion; no F1 query is used.

The source module Raw13Coupled6UnaryRecursion.lean formalizes the finite identities and the arbitrary-tail recursion directly. Source acceptance pending.
