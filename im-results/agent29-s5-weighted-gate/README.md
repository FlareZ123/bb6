# Sweeper S5: exact weighted reset criterion

**Result:** Lean 4.36.0-rc2 proves the exact all-time digit-model stopping equivalence, reducing the root problem to three arithmetic reset gates. Authentic root avoidance remains open. Literal table: `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF` (historical roster row 458). The [pinned upstream separator rules](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF.lean) give the D/FR model and three-step seed. Source connection is mathematical identification, not a combined original-machine Lean theorem.

State (L,p,R), positive auxiliary run lengths nearest first. D digits (p::map(subtract 1,L), map(subtract 1,R)). Seed ([],2,[]). Bump(k,S) adds k to head, creating [k] if empty and k>0. Pop on empty returns zero.

* p>=2: k=floor(p/2); bump k on L and R; p:=p mod 2.
* p=1: pop L into p; prepend 1 to R.
* p=0,R=[]: pop L into l; p:=l+2.
* p=0,R=[1]: pop L into l; p:=l+5; R:=[].
* p=0,R=1::nonempty: halt C1.
* p=0,R=2::T: pop L into l; p:=l+3; R:=bump(1,T).
* p=0,R=r::T,r>=3: if T=[], L:=bump(4,L), p:=r-3; else reverse T=z::Z, L:=Z++[r-2]++bump(4,L), p:=z-1. R:=[1].

W(L)=sum_i 2^i L_i, P=p+2W(L). A complete odd transfer+pop halves P+1. A sequence of n odd shifts reaches the fatal state L=[],p=1,R nonempty iff P+1=2^(n+1) and (n>0 or initial R nonempty).

Right bounce r>=3, m=length T, U(T)=sum_j 2^(m-1-j)T_j: P'+1=2^m(P+r+6)+U(T). It begins a fatal odd cascade iff 2^m divides U(T) and P+r+6+U(T)/2^m is a power of two.

Root halts iff some reachable p=0,R nonempty satisfies:
1. R=[1] and W(L)+6 is a power of two;
2. R=2::T and W(L)+4 is a power of two;
3. R=r::T,r>=3, and the bounce test above.

Immediate C1 halt is preceded by an odd fatal cascade; the first bad rank had to be created by one of these reset families. Empty-right zero-cursor states are unreachable from seed; E0 halt impossible.

[Lean source archive](lean-source.tar.gz), local and Git blob SHA 7fc1ed6e7d66e5c114825cc7f4a9eaa8e4516ea2. Extract and compile S5Rank, S5Digit, S5Phase in that order using LEAN_PATH=. lean -o module.olean module.lean. S5Rank.odd_phase_fatal_iff, bounce_rank, bounce_fatal_iff use only propext, Quot.sound; seed_halts_iff_reset, seed_digit_halts_iff_reset, no_haltE only propext, Classical.choice, Quot.sound. No native_decide or sorryAx.

Finite search: 100,000,000,000 outer events survived, representing 119,652,478,686 grouped transitions after authentic D seed. Endpoint p=73834,L=[303105409,11203690789,25629071831,26622669872],R=[1]. Max observed run/cursor 63,757,711,185, max combined depth 35. Search is evidence only. Remaining task: prove reset gates avoided on actual root, or find witness. Small-modulus filtering alone is unlikely to suffice (sampled quotients covered all mod64 residues).
