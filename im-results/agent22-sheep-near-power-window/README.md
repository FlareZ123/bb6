# Sheep: exact offset-driven terminal-free windows

**Agent 22, 24 November 2026.** Local Lean 4.36.0-rc2 checked theorems importing the unmodified repository `SheepEven.Step` and `Steps`. For every sufficiently large valuation, there is a provably growing window of successful raw *section returns* after an exceptional cofactor-three state, and after generic near-power states. The adaptive version computes an often much longer certified window using only the low offset. These are intermediate structural results, not a blank-root decision.

## Uniform theorem

Write a nonterminal section source as x=2^a*u, u odd >=3. The first actual return is x+B, where B=a+3 if u=3, and B=a+(u-1)/2 otherwise. Choose L with 0<B<2^L and define

    D(L,r) = (r+1)*L + r*(r+1)/2.

If D(L,r)<=a, then every one of the first r+1 raw section return endpoints exists, has odd cofactor >=5, and is neither a halting power 2^j nor a special 3*2^j for any j. Thus, for u=3 or any fixed odd u>=5, the time from the near-power source to the next possible special/terminal event is Omega(sqrt(a)) in raw section returns. The theorem applies to actual trajectories from a supplied source, including a source reached by the genuine blank run, with no representative selection. It does not prove that the blank run reaches such a source.

## Adaptive theorem (exact source equations)

For positive B, introduce the *generic algebraic extension* G(B)=B+b+(v-1)/2 where B=2^b*v and v is odd. In this auxiliary low-offset calculation the generic formula applies even at v=1 or 3. It is not the real Sheep section map on B.

For a split x=C*2^A+B with C>=3 and 0<B<2^A, the true odd cofactor is C*2^(A-b)+v, odd and at least five. Its actual next state is exactly

    C' * 2^(A-b-1) + B'
    C' = C*(2^(b+1)+1)
    B' = G(B).

Let B_r=G^r(B), and c_r=sum_{i<r}(v2(B_i)+1). If c_r<=A and B_r<2^(A-c_r), the entire r-step source path exists and all its endpoints (including the start) are generic. The endpoint equals C_r*2^(A-c_r)+B_r, with C_r=C*product_{i<r}(2^(v2(B_i)+1)+1). The Lean statement `low_transport` gives the actual Steps witness and a safe endpoint; the displayed product follows immediately by iterating the separately checked one-step equation. Monotone B_i and strictly increasing precision costs imply that checking the final inequality suffices for every prefix. Apply this to C=3, A=a, B=a+3 immediately after a special source; the generic near-power case uses C=u and B=a+(u-1)/2.

For the uniform formula, if B<2^L then 0<G(B)<=2B<2^(L+1) and b+1<=L. Inductively one may spend at most L+i precision at step i and needs L+r bits for the final offset; their sum is exactly D(L,r). The proof uses no probability, no experimental growth assumption, no modular-residue catalogue.

## Reproduction and practical effect

Restore the exact original `SheepEven.lean` from ../agent16-sheep-even-return (source SHA256 82d1b77cbd8d2071b624834de5796697f6d3b02941ecda08d7f0075cbea846d5) and compile it to SheepEven.olean. Run reconstruct.py here and copy NearPowerWindow.lean to the same Lean module directory. With LEAN_PATH=. run lean NearPowerWindow.lean under 4.36.0-rc2 (commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). The source SHA256 is 13438b2416415dfb9533ff99301b7e9852bf78d2fdf843c6a9981fe6b1b7fe1e. All eight printed theorem profiles contain only propext, Quot.sound, and (where needed) Classical.choice. No sorryAx, native_decide, or unapproved axioms. The physical machine-to-section equivalence is the prior source-accepted [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), not a new upstream CI run.

The accompanying check_window.py computes the uniform and adaptive windows without forming the large state, and independently replays each demonstrated adaptive prefix through a=10000 using the full integer states and exact split equality. Observed results, r after the first special return:

| a | uniform r | adaptive r |
|---:|---:|---:|
| 100 | 8 | 42 |
| 1201 | 38 | 486 |
| 2659 | 61 | 1083 |
| 10000 | 127 | 4150 |
| 100000 | 430 | 41569 |

The 100000 case is an offset-only calculation, not a literal full-state replay or kernel evaluation of its numerical result. The general certificate theorem is kernel checked independently of these examples. The adaptive inequality is a sufficient event-free window and its first failure does not mean an event has occurred.

## Research use and remaining gap

This is a quantitative forward counterpart to the existing exceptional-source inverse cutoff and finite-word lifting, and a complement to Agent16's band-residence upper bound on raw return counts. It supplies an explicit lower bound on the number of raw returns separating high-valuation near-power sources from any subsequent terminal or exceptional state. It can prune any proposed finite inverse route whose alleged predecessor violates that bound, and can skip long event-free windows after an actual near-power source using only a small offset.

The theorem does not bound the number of returns between arbitrary states, establish a universal linear growth rate, or rule out the next event beyond its window. In particular it does not eliminate any complete outstanding blank-root halting family. The remaining question is still whether the fixed orbit beginning at section 5 (first even state 10) ever reaches a power. External academic novelty is unassessed; retain this as intermediate research.
