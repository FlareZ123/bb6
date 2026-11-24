# Density-one halting for every fixed finite suffix of Cryptid D

Agent 3, 2026-11-24. Status: rigorous mathematical proof with a reproducible finite integer certificate (Python, not yet an end-to-end Lean kernel proof). Uses the previously kernel-checked original-machine first-exit and source recurrence. Does not decide any of the four distinguished integer roots or the BB(6) upper bound.

## Theorem

For the literal machine D = 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---, fix any finite binary suffix v. Let H_v be the set of integers n >= 2 for which F/0, blank left tape, and right tape 1^n 0 v followed by implicit blanks eventually halts. Then H_v has natural density one. In fact there is an absolute epsilon > 0 such that the count of n in [2,N] outside H_v is O_v(N^(1-epsilon)).

This removes the bounded-suffix-complexity hypothesis of Agent26's [conditional bounded-survival cover](../im-results/agent26-d-halting-density/README.md). The power saving is extremely small; it is not a practical bound on a particular integer input. The result concerns prepared tapes, not the initial blank machine. The positive proportion of known halting cylinders alone would not prove this theorem.

## Source recurrence

Use canonical suffix s = empty or a word beginning 0 and ending 1; s includes the delimiter after the maximal unary run. A finite binary word is read nearest bit first with implicit far zeros, represented equivalently by the natural number whose binary bits are in that order (little endian). Let R(s) = length(trim(s)) + 2 * number of occurrences of 011 in trim(s), where trim removes far zeros. Occurrences may be counted at all indices; 011 is non-self-overlapping.

We use the original-machine uniform affine recurrence of [Agent32](2026-11-24-d-global-affine-completeness-agent32.md) and its [one-cell exit theorem](../im-results/agent32-d-onesided-total/README.md). The underlying literal prefix and B/D sweeps are in Boundary.lean (Agent31), with the A0 zero-close case in BoundaryExtra.lean (Agent36). For n = 3k+d_r, d=(3,4,2), r = n mod 3, the recurrence either halts uniformly in k, or gives a positive-time return (8k+c,s'), c >= 3. Here is a deterministic choice of that recurrence, specifying the normalization used in the finite certificate:

* B (r=2): remove the first zero from s (implicit when empty), then remove all leading ones from what remains; their count l is added to 8k+9.
* E (r=1): original prefix_E produces state E scanning 0, left stack 00(10)^(4k+3)11, right tail s[1:]. Regard scanned bit plus right tape as word w, initially s. Take successive one-cell first-left-exits, independent of the left context by the source theorem. On consuming p left cells, the next word is the consumed bit prepended to the written right word returned by the exit. The explicit guard is 00101010. Stop at the first p>=2 even with state B or D scanning 0, or at a halt. At a sweep endpoint the left stack is (10)^(4k+3-(p-2)/2)11. The B/D sweep gives 8k+11-p ones, then the right tail of the scanned zero. Normalize by removing l leading ones from that tail, giving c=11-p+l. The checked abstract guard below proves every nonhalting exit chain stops by p=8.
* A (r=0): prefix_A gives A0 with left stack 0(10)^(4k+3)11 and right tail v=s[1:]. Greedily parse 10 and 111 tokens in v; a final implicit zero can complete a final 10. The source token rules add one and four pairs respectively, hence add 2 and 8 to the eventual unary constant. When v starts with zero (including implicit blank), close with the A0 zero-close B/D sweep, giving c=11+token contribution+l with l leading ones of v[1:]. Otherwise the residual begins 110 (including implicit blank after 11); the source three-step A-to-E rule adds one pair. Apply the preceding E procedure to the suffix after the two ones, including its zero delimiter, and add 2+token contribution to c.

These are source-derived operations, not a fit to an observed orbit. The one-cell exit theorem gives finite termination of each exit for every finite word; the token parser terminates by decreasing remaining length. Positive live returns cannot coexist with a finite halt because the original source freezes at its halt. Thus a nonhalting trajectory gives infinitely many returns. The code evaluator.py implements precisely this chosen recurrence; it is only used to certify a short residue-word witness and small root anchors, not to infer drift from samples.

## Finite abstraction and certificate

Let M=2048, N=4096. For a word with little-endian value w, its class is w if w<M, otherwise M+(w mod M). Thus the class retains the first eleven bits and whether additional nonblank content exists. Even classes correspond to canonical delimiter words. The exact rank formula is
    R(0)=0,
    R(w)=R(floor(w/2))+1+2*[w mod 8=6], w>0.
The following edge operations record destination class and an upper bound on rank change.

1. Pop: on short classes compute the exact destination and rank difference. On long class M+p, the only possible classes after dropping the scanned bit are floor(p/2)+M/2, floor(p/2)+M, floor(p/2)+M+M/2. Rank gain exactly -1-2*[p mod 8=6].
2. Push b: for zero use (b,b); otherwise prepend b, with rank gain 1+2*[b=0 and old prefix=11]. Class follows directly by modular reduction. Replace scanned bit b: exact short difference, or twice the change in the indicator of prefix 011 for long words. These formulas cover every physical finite word including all blank padding.
3. Canonicalization strips leading ones until even. Each such pop loses exactly one rank unit. At the long all-ones prefix class, allow every even output class with gain -11; the first eleven pops are forced, and further ones can only reduce rank. In all other cases the number of known leading ones decreases, giving finite recursive composition. Dropping fixed-length prefixes likewise composes pop edges.

Construct an abstract exit relation X[q,c] whose entries (r,j,g) bound the rank gain of a finite first-left-exit starting in state q, class c, and ending in r with written right-word class j (not including the consumed left bit). For an immediate left transition the exit is a replace edge. For a right transition writing b and entering r, pop the scanned bit, take a first-left-exit in r, push b onto its written word (return to the original cell), then take a second first-left-exit. A finite returning computation has this decomposition: the first return to the original cell occurs before its first departure left. Induction on the number of primitive transitions proves that any relation containing the immediate exits and closed under this two-exit rule overapproximates every actual finite returning exit. Halting exits require no return row.

The exact integer checker saturates X by these rules and explicitly checks closure, with no simulation horizon. For each even class it propagates X across the E guard, appending the consumed guard bit via push. Each endpoint satisfying the B/D sweep test contributes pop+canonicalization edges. It asserts no unresolved guard state at p=8. An actual nonhalting exit must be represented, so this assertion suffices together with source exit totality. Every E return has a matching abstract destination and rank upper gain.

The A parser is treated as a second finite relation: its close branch drops two bits (delimiter and zero) and canonicalizes; its E branch drops three bits and uses E; its 10/111 token branches drop respectively three/four bits and push a zero before recursively parsing. Closure is checked independently after saturation. Induction on the remaining concrete token count proves the A abstraction sound. B is just pop+canonicalization.

The resulting relations have the following exact sizes and extrema, as reproduced by certificate.py:

| relation | rows (distinct input/output pairs) | minimum stored gain | maximum stored gain |
|---|---:|---:|---:|
| X | 22638 | | |
| A | 181461 | -18 | 6 |
| E | 10347 | -2 | 11 |
| B | 22529 | -14 | 0 |

The minimum stored gain is not a lower bound on actual rank loss. It is a lower bound on the *upper bounds* that the checker assigns, which is what the exponential argument below needs. In particular every successful return increases rank by at most 11.

For each class c let L(c) be its exact short rank or 12 for a long class. A halt has next rank zero and hence gain <= -L(c). Add this as an extra pessimistic branch even where no halt is possible. Let V_0(c)=0. Recursively set

    V_{d+1}(c) = sum_{r=0,1,2} max(
        -3^d L(c),
        max_{(j,g) in table_r[c]} (3^d g + V_d(j))
    ).

This bounds the sum of rank changes over the 3^(d+1) possible residue words. More precisely, for each actual starting word, choose one matching upper-gain edge at each vertex of its ternary continuation tree; a halt is absorbing with subsequent gains zero. The witness choice at each vertex is made before its future residue choices. The sum of the resulting per-path upper gains is bounded by V by induction. Every five-edge path upper gain G is between -90 and 55, since all stored gains and fake-halt gains lie in [-18,11]. (The largest short rank is 17.) Every actual rank change is at most G, including arbitrarily large losses. The verified maxima over the 1024 long even classes are

    d     0   1   2   3   4    5
    max   0  11  16  29  27 -118.

Thus for every long concrete suffix the five-step expected rank change is at most -118/243 under independent uniform residue choices. The calculation covers unbounded suffix lengths: only the prefix abstraction is finite. No conjecture on bounded suffixes or random behavior of a fixed integer orbit enters the proof.

## Residue measure is exact

Each prescribed sequence of t residue choices up to a halt (extended arbitrarily after halting) corresponds to exactly one starting residue class mod 3^t among n>=2. Induction: for a fixed live prefix of length j, write all starting inputs in its cylinder n=a+3^j h, where a is the smallest representative >=2 and h>=0. The endpoint unary number is b+8^j h, with common suffix. Because 8^j is a unit mod 3, prescribing the next residue selects exactly one h mod 3; substituting h=i+3h' gives the next affine cylinder. The smallest representative is valid because n>=2 and every return has c>=3. Halt cylinders extend into all three child classes. This is the same affine arithmetic as RouteArithmetic.lean and Agent26's complete cylinder proofs, and holds for mixed A/E/B words. Therefore for each fixed t the uniform 3-adic residue measure of survival equals its natural density on positive integer inputs. The stochastic suffix process is an exact counting device for all residue classes, not a probabilistic assumption about the four roots.

## Quantitative recurrence and absorption

Sample the suffix process every five returns, with halt absorbing. Let a=100001/100000, q=249999/250000, and define W(s)=a^R(s) on live suffixes, W(halt)=0. For every integer -90<=G<=55 the exact rational certificate verifies
    a^G <= 1+G/100000+4095/10^10.
Since actual rank gain <=G, and zero after halt is even smaller than a^G, the previous upper sum gives, for each long suffix,
    E[W(next)]/W(s) <= 1-118/(243*100000)+4095/10^10 <= q < 1.
Let S be the finite set of live suffixes of length at most 11 (rank <=17). Starting outside S, let tau be the number of sampled blocks before first reaching S or halt. Induction using the killed process gives P(tau>t) <= W(s)q^t for t>=0. This gives almost-sure return to S or halt, and for z>1 with zq<1,
    E[z^tau] <= 1+(z-1)W(s)/(1-zq).
The same bound holds trivially when starting in S or halt.

From S, eleven consecutive B choices remove every zero delimiter in the original suffix, absorbing intervening runs of ones into the unary count; further B choices preserve the empty suffix. The checker explicitly replays a 108-residue E/B halting word from empty, with representative
    536381281436517453494167225374698024519484110452372
and modulus 3^108. Its finite path is uniform in the unary parameter by the source recurrence. This gives success probability at least p=3^-119 within 120 returns (24 sampled blocks), from every S state. Equivalently one can use a suitable finite source-certified cylinder from the earlier RouteBridge.lean. After a failed attempt, rank is at most 17+120*11=1337, and the checker verifies a^1337<2.

Repeat the following cycle from S: attempt for 24 blocks; if still live, wait until S or halt, then repeat if live. Set z=1+p/10^9. We have 1-zq >= (1-q)/2=2e-6 and z^24 <=1+48(z-1) (binomial expansion for this range). Conditional on failure of the attempt, the waiting time has z-moment <=1+2(z-1)/(1-zq). Thus the expected z^duration times the indicator that a cycle fails to halt is at most
    z^24 (1-p) [1+2(z-1)/(1-zq)] <= 1-p/2.
Indeed the first factor <=1+48p/10^9, the last <=1+p/1000, and their product <=1+p/2 for 0<p<=1. The unconditional z-moment of the duration up to the end of the cycle (or earlier halt) is at most z^24[1+2(z-1)/(1-zq)]. Summing the geometric series of successive failed cycles, and using the initial waiting-time bound, shows E[z^T] <= C_s < infinity for the number T of five-return blocks to halt. Consequently P(T>t) <= C_s z^-t. In particular there is no positive-measure nonhalting prepared-suffix set.

Finally survival through 5t returns is a union of at most 3^(5t) C_s z^-t residue classes mod 3^(5t). Choose t=floor(log_3(N)/5) so the modulus is <=N. Each class has at most N/3^(5t)+1 representatives in [2,N], hence the nonhalting count is <=2N C_s z^-t = O_s(N^(1-epsilon)), epsilon=log(z)/(5 log(3))>0. This establishes the stated theorem for every fixed finite suffix v, by trimming 0v to canonical s.

## Reproduction and proof status

Run python3 certificate.py in [agent3-d-density-drift](../im-results/agent3-d-density-drift/). It saturates and checks the finite relations, checks the guard, computes all five Bellman layers, checks the explicit halt witness and exact rational inequalities. Typical local runtime a few seconds. The computation uses only Python's exact integers, finite dictionaries and Fraction; it is deterministic and independent of root trajectory simulation. The proof above is a computer-assisted mathematical argument; the new 11-bit certificate and probabilistic/counting conclusion have not yet been completely formalized in Lean. The previously established machine semantics and uniform-return lemmas are Lean-certified. All claims are conditional only on those checked source lemmas and the reproducible finite certificate, not on additional unproved mathematical hypotheses.

## Implication for BB(6)

Any infinite orbit of a distinguished integer root, if one exists, lies in an exceptional set of zero density, with a quantitative power-saving counting bound. This does not rule out any particular root. The missing decisive step is to show each specific integer residue stream eventually enters a halting cylinder, or to give a root-specific nonhalting proof. It would be unsound to infer that 5,9,15,39 halt from density one. No global BB(6) numerical bound is changed by this theorem.
