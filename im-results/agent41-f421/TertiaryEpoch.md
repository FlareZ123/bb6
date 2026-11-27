# F421 tertiary countdown after secondary exhaustion

**Status:** The full guarded positive tertiary countdown is now source-level kernel-checked in `F421Epoch.lean` (`tertiaryEpoch`). The authentic seed remains numerical. At the authentic odd-65700 frontier, a tertiary countdown of 2^8214−1 cycles is safe under the proven guards. The conditional tertiary-zero crossing is now derived in [TertiaryZero.md](TertiaryZero.md); the authentic blank-start-to-seed bridge, the next secondary primary guard, whole-machine verdict and BB(6) maximality remain open. No primitive-step total or new BB(6) bound is claimed.

## Tertiary cycle

P=10, Q=01, Z=00, H=11. The zero-marker regular prefix is P^a Q^b ∏P^p Q^q, near-to-far. The tail is

    P^x Q P^y H ∏ Q^z_i Z^(1+f_i) P^r_i H U

with S=∑f_i2^i>0, least set bit j, x,y≥3, z_i≥3 at visited cells, all r_i≥2.

1. Odd e maps the regular crossings Q^q P^p to P^q Z Q^(p−1). At the final Q P turn (011), the untouched suffix half-shifts: after P Q^(a+1), the marked prefix consists of (b,p_0−1),(q_0,p_1−1),…,(q_last,x−1); then the unmarked separator (1,y), and cells (z_i+1,r_i+1,f_i). The shifted suffix U retains its pending alignment from H. Drain A restricted to the marked prefix (separator and subsequent cells treated as untouched suffix). The far cell survives and its q becomes x.
2. Even d traverses the unmarked regular cells and separator P^1 Q^y to the first marked tertiary cell j. The separator undergoes intentional nonterminal P deletion, leaving Z Q^y. Regular P lengths decrement and become marked. The lower tertiary cells become (z_i,r_i+1,1); at j (z_j,r_j+2,0), higher unchanged. Drain B restricted to the regular prefix. The far cell q becomes x+1.
3. Odd d turns on 00 at the barrier (Q^q consumes first zero of Z in continuing tokens; then second zero and first zero of Q^y form 00). Same regular crossing map, followed by P^(x+1) Q and the untouched suffix beginning at the remaining 1 of Q^y. Half-shift gives P^(y−1) H and restores the higher suffix alignment. Affected transformed cells map (z,r+1,f) to Q^(z−1) Z^(1+f) P^r H. Drain C over all resulting marked regular cells.

Thus x'=x+1, y'=y−1, S'=S−1; i<j: z'=z−1,r'=r,f'=1; i=j: z'=z−1,r'=r+1,f'=0; higher unchanged. Both half shifts cancel on arbitrary zero-padded U. Over k cycles n_i=(S>>i)-((S−k)>>i), t_i=floor(((S>>i)+1)/2)-floor((((S−k)>>i)+1)/2); z'=z−n_i, r'=r+t_i. Tail guards hold through S decrements from y≥S+2, x≥3, z_i≥(S>>i)+2, r_i≥2. A visited z_i is at least 3 before its last visit. Count per cycle 3+H_A+H_B+H_C principal macros, not a primitive total.

## Primary invariant allowing arbitrary terminal deletions

For m regular cells M=2^m. Keep the three farthest as fixed suffix, positional scales B_i=4,2,1 near-to-far. For k remaining cycles require a=2M−1, b≥7 with b+1 divisible by8; all p≥3; each head q≥7 with q+1 divisible by8; fixed suffix q_i≥3 B_i k+B_i+2.

For k>0 the A input's far three P lengths (old q_i) are ≥4B_i+2. They survive A and B: subtract (2B_i−1), then 1, then (2B_i−1), leaving q_i−4B_i+1≥3. Both A and B enter head with terminal count H=7. All remaining A P inputs (old head q and leading b) are −1 modulo8.

The complete all-marked drain (BoundaryEpoch.md) processes far-to-near: cap=2H+1, t=(min(p,cap)+1)//2, H'=H+t; remove zero P, merge Q masses into preceding Q. If H≡3 mod4 and p≡7 mod8, deletion is terminal (p odd), t=(p+1)/2 divisible by4. A survivor has t=H+1 divisible by4 and residual p=p−cap a positive multiple8. Thus H'≡3 mod4. After A survivors decrement 1 before B and are again −1 mod8. B is safe by the same induction. All B head survivors p≥8; fixed far p≥3.

Let L be number of B survivors, N=2^L≤2M. A surviving cell gets at least its new positional scale terminal visits (count-plus-one doubles at farther survivors and never decreases at deletions). Q masses only increase in A/B. Hence q_A≥2+B_A, q_B≥2+2B_B since B_A≥B_B. C has L marked cells: its P inputs are leading b_B and preceding (nearer) B survivor q_B. At scale B the latter is ≥2+4B, so full budget 2B−1 leaves ≥2B+3. The nearest has b_B=a+2+H_A+H_B+merged masses≥2M+15 and budget N−1≤2M−1. Thus C has no deletions and all p≥3.

New a=2N−1, b'=N+3+2(H_A+H_B), b'+1 divisible8 (N multiple8, H_A,H_B≡3 mod4). For head q'=p_B−1+B, both p_B and B divisible8, q'≥7. For the far three q'=q_i−3B_i, retaining next budget. This proves induction through k=0, allowing arbitrary head terminal deletions. The far regular q_B=x+1 transfers into tail, so primary computation is independent of x.

## Authentic seed

Secondary-zero checkpoint hash f5e445d70cf1b2fc1982201911c6557b6c2b9fd5a1b9ee082e21be31758f2f87 reproduced byte-for-byte with closed recurrence from PrimaryGuard.md. Ten subsequent odd macros and final regular drain give odd65700: a=15,b=39, three primary cells, 8214 tertiary cells all f=1. Serialization pair then space then decimal run length per newline has SHA256 a74ba0026d9a3d59b37216703669dd8d7c59f552c63cd5fa3c7efd38de75fab2. Exact guard checks: x//S=130,y//S=35,min z_i//(S>>i)=20; fixed suffix q_i//(3B_iS)=4,10,10. All actual inequalities checked. One exact authentic cycle and 300 randomized guarded exact cycles matched. Thus the conditional theorem covers S=2^8214−1 decrements and reaches odd principal macro 65700+2S followed by final drain, with no F1 query.

TertiaryGuard.lean formalizes modular drain, Q-budget growth, crossing and leading modulus arithmetic; Lean 4.36.0-rc2 locally accepted, standard axiom profiles. The source bridge and entire positive countdown are now proved in `F421EpochWords.lean`, `F421EpochCycle.lean`, `F421EpochGuard.lean`, `F421EpochInduction.lean`, and `F421Epoch.lean`, checked locally against the exact compiled repository dependency closure (CI 45961519738 artifact). No extra axioms. `tertiaryEpoch` takes the natural counter n, the primary invariant, x≥3, y≥n+2, and recursive tail budget. It returns a source-machine run of at least n primitive steps to a zero-marker tertiary frontier with primary invariant at k=0, x+n, y−n, all tail bits clear. It does not instantiate the authentic seed. The subsequent `tertiaryToSecondary` theorem in F421ZeroGuard.lean now includes the zero-boundary crossing with one spare primary budget unit, preserving tail width.

The crossing at zero no longer requires explicit primary-head iteration: see TertiaryZero.md for the universal guarded crossing and the autonomous normalized head recurrence. The next secondary counter has 8215 set bits; its tail budgets hold, but its primary budget is unresolved.
