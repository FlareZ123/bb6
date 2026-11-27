# F421 tertiary-zero crossing and autonomous normalized head

**Status:** conditional paper-level crossing theorem using the existing frontier and drain identities. Standalone arithmetic is checked by Lean 4.36.0-rc2. The authentic tertiary tail is computed exactly; its primary endpoint is not computed. No original-machine composition, whole-machine verdict or new BB(6) bound is claimed.

## Zero crossing without computing the primary endpoint

Use P=10,Q=01,Z=00,H=11. Let the zero-marker primary prefix be P^a Q^b followed by m cells P^p Q^q, m≥3, M=2^m, a=2M−1, b≥7 with b+1 divisible by 8, all p≥3, head q≥7 with q+1 divisible by 8, and far three q≥2B+2 at scales B=4,2,1. These follow from the tertiary guard at remaining count zero. Suppose the tail is

    P^x Q P^y H ∏ Q^z_i Z P^r_i H Q^z* Z P^r* Z P^v H V

with x≥3 and y,z_i,r_i,z*,r*,v≥2.

The odd e crossing produces a=1,b=old a+1 and marked primary cells (old b,p_first−1),(old q_first,p_next−1),...,(old q_last,x−1), followed by an unmarked separator (1,y), unmarked cells (z_i+1,r_i+1), and (z*+1,r*). The suffix shift follows directly by pairing adjacent bits across the H and Z boundaries. Drain A removes only marked primary cells. Its three far cells survive because the input P lengths exceed their caps 2B−1. The head deletion parity is safe by TertiaryEpoch's mod-eight guard. Write H_A for total terminal visits, r_A for merged leading Q mass, L for surviving primary length and N=2^L. Then N≤2M, H_A+1≥N, all surviving p≥3, and each q≥B+2 at its new scale B. The final q is x.

The next odd d crosses all unmarked tail cells to the Z barrier, and cancels the half shift. The new marked primary has L cells obtained by crossing (b_A,p_Afirst−1),(q_Afirst,p_Anext−1),... . The new tail is

    P^x Z P^y ∏ Z Q^z_i P^(r_i+1) Z Q^z* P^r* Q P^v H V .

For any nonnearest marked cell the P input is the preceding A survivor's q, at twice the new scale B, hence at least 2+2B. Its drain cap is 2B−1, leaving ≥3. The nearest P input is b_A=2M+H_A+r_A; its cap N−1 leaves ≥N. Thus drain C has no deletion, exactly N−1 terminal visits, and produces a'=2N−1, b'=N+1+2H_A≥3N−1; all p≥3 and q≥B+2. The total is H_A+N+1 principal macros, including the two odd crossings. This proves safe passage for every primary endpoint in the stated guard, rather than assuming a particular uncomputed endpoint.

The new secondary counter has n+1 set bits, where n is the number of tertiary cells. For the authentic n=8214, S=2^8214−1, the new counter is T=2S+1=2^8215−1. Apply the exact tertiary tail endpoint x'=x+S,y'=y−S,z_i'=z_i−floor(S/2^i),r_i'=r_i+floor((floor(S/2^i)+1)/2). The authentic untouched U begins Q^131061 Z P^1671169 Z P^229369 H. The next secondary tail satisfies x'≥T+4, y'≥T+3, and its new r_i≥floor(floor(T/2^i)/2)+2 for every i. These are sufficient tail budgets for the entire secondary countdown; the primary guard for that countdown remains open. In particular the stronger divisibility and suffix P budgets of PrimaryGuard.md are not established by this crossing.

## Normalized autonomous head

Far-to-near, encode the head q values by u=(q+1)/8 and append the ghost (b+1)/8. The initial list at odd 65700 is [5]. After the three fixed far cells, each marked drain starts with h=(H+1)/4=2. For each u in order, if u≤h delete it and set h←h+u; otherwise emit u−h and double h. Run this twice from h=2, obtaining a residual list bs and final accumulators A,B. The next normalized list is

    [bs[i]+2^i for i=0,...,len(bs)−1] ++ [2^len(bs)+A+B].

Indeed A and B account for terminal deletions as well as survivors; the final crossing restores q from the B-surviving p, adding the new positional scale. The appended term is the new ghost from the exact leading b formula. The sum increases by 3+2^length(new list) and length increases by at most one. If the farthest head u>4, it survives both drains and changes to u−3 regardless of all nearer entries. TertiaryHead.lean checks these arithmetic identities, as well as zero crossing inequalities and protected far-cell update arithmetic, using only standard axioms. This does not formalize the word-return composition.

## Evidence and reproduction

Run tertiary_zero.py for 300 deterministic randomized guarded zero crossings against the exact principal macro engine, and simultaneous normalized-head recurrence comparisons. Generate prefix-state.txt as in BoundaryEpoch.md, then run tertiary_zero.py --authentic. The seed digest is a74ba0026d9a3d59b37216703669dd8d7c59f552c63cd5fa3c7efd38de75fab2. All authentic zero-tail and new secondary-tail guards pass. The extra exact zero-crossing experiment uses a synthetic admissible primary with the authentic tail; it does not pretend to compute the actual primary after S decrements. Lean TertiaryHead.lean compiles locally (standard axioms only). Next: solve the primary endpoint or derive a stronger inductive guard at the secondary boundary, and formalize exact source composition.

## Source-level proof completed

`F421ZeroWords.lean` proves the exact shifted suffix, secondary cell word, odd-d crossing, and whole zero cycle; `F421ZeroGuard.lean` proves the guard and combines it with a slack-preserving positive epoch in `tertiaryToSecondary`. The theorem accepts `primary (n+1)` rather than `primary n`, returns the same tail width with all bits clear and the new secondary word, and gives at least n+1 primitive source steps. The authentic seed has ample extra budget. Local Lean 4.36.0-rc2 checked both files against the actual CI source closure, with standard axioms only. The blank-start-to-seed bridge and the next secondary primary guard remain unproved.
