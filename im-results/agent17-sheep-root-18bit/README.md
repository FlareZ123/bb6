# Authentic Sheep blank-root coverage through 18 binary bits

**Status (9 November 2026): exact finite computation, independently cross-replayed; no unbounded nonhalting theorem.** The first-even Sheep orbit from the *actual blank-section entry* (x_0=10) visits **every even residue modulo (2^{18})** by section index (1,587,683). This is a strictly stronger, independently checked finite-root analogue of Agent22's earlier modulo-(2^{15}) coverage. It is a quantitative obstruction to low-precision, root-specific congruence and short symbolic-word avoidance; it leaves BB(6) and the Sheep halting decision open.

## Exact claim and computed witnesses

Let (x_{n+1}=E(x_n)) be Agent16's source-certified first-even Sheep return, where for even (x=2^a u), odd (u), (age1), (uge3),
[
F(x)=egin{cases}x+a+3,&u=3,\\x+a+(u-1)/2,&uge5,end{cases}
qquad
F(x)-1=2^h v,quad v 	ext{odd},qquad E(x)=1+3^h v.
]
If (u=1), the genuine section halts, so (E) is undefined there. The original-machine connection and the all-time blank-return equivalence were already Lean-certified by Agent16 in [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547); the present claim concerns additional **finite computation of its deterministic orbit**, not another source theorem.

Two independent GMP/C++17 exact-integer implementations produced the following earliest complete-coverage indices. The SHA256 is over the first-visit indices for even residues (0,2,ldots,2^p-2), in increasing residue order, each encoded as little-endian unsigned 32-bit.

| Precision | Number of even residues | Last first-visit index | SHA256 of first visits |
| --- | ---: | ---: | --- |
| (p=16) | 32,768 | 374,581 | `86f41e4cd8b06f5b0a8d327e0acc506aadca98e0068016a29d0507ec58a4554e` |
| (p=17) | 65,536 | 710,665 | `1ea110f0b7763723599999566227bc46474fab4b9234ffc4779b5a8550bd1157` |
| **(p=18)** | **131,072** | **1,587,683** | **`96bddd4a8e73717ccc7e889eccb9f033cb7ba696bd732d46b92f25f571cb77be`** |

Both implementations agree on the exact (p=18) hash and last index. From indices (0) through (1,587,692) inclusive, the independent **literal odd-step** implementation encountered neither a halting power (odd cofactor one) nor the exceptional cofactor-three source. Its computed successor (x_{1,587,693}) has 1,273,726 binary digits. Independently, the accelerated implementation observed (operatorname{bitlen}(x_{1,500,000})=1,203,652) and no halt up to the later complete-coverage point. Since the exact even return strictly increases, any genuine later halting power (2^j), **if one exists**, must have (jge1,203,652). This explicit exponent bound is intentionally conservative: it uses the reported bit length of a nonterminal state, without extrapolating an unverified state value.

## Exact finite symbolic consequence

Agent22's [canonical 2-adic branch-cylinder theorem](../agent22-sheep-2adic-bernoulli/README.md) identifies each finite generic itinerary word (w=((a_1,h_1),ldots,(a_t,h_t))) with one residue class modulo (2^{C(w)+1}), where
[
C(w)=sum_{i=1}^t(a_i+h_i+1),qquad a_ige1, h_ige0.
]
Every word of cost (C(w)le17) therefore corresponds to (2^{17-C(w)}) distinct even residue classes modulo (2^{18}). Since each such class occurs in the actual blank orbit by index (1,587,683), each word occurs at least (2^{17-C(w)}) times as an actual **generic** prefix among those starting indices. The nine extra checked states through index (1,587,692) guarantee all words of cost at most 17 (length at most eight) have sufficient lookahead and encounter no exceptional branch. The number of distinct nonempty such words is
[
sum_{c=2}^{17}2^{c-2}=65,535.
]
This conclusion strengthens the earlier cost-14 finite universality of Agent22; it does **not** prove that the infinite blank orbit is dense, normal, nonhalting, or that it ever visits a halting power.

## Reproduction and evidence boundary

- [root_even_census.cpp](root_even_census.cpp): accelerated formula for (E), GMP exact integers, separate completeness counters for precisions 16, 17, 18, no floating point. Captures the earliest first-visit of each even class and hashes the canonical little-endian list. The default limit is 2,500,000 and the program exits once the (p=18) census is complete.
- [root_literal_verify.cpp](root_literal_verify.cpp): independent second implementation of the section dynamics, repeatedly applying the **literal odd source formula** (tmapsto(3t-1)/2) until reaching an even section state; does not use the accelerated (3^h) identity. Its counter and first-visit SHA256 agree at (p=18) and it replays nine extra even states.
- Both were compiled and executed locally with C++17, GMP, OpenSSL libcrypto under Linux. The (p=18) claim is backed by duplicate exact-int arithmetic and a shared canonical first-visit hash; it is **not a Lean-kernel-certified million-step trace**. The original-source equivalence is Lean-certified separately.

For a typical Linux compiler with GMP and OpenSSL development libraries available, build each translation unit using C++17 and link `gmpxx`, `gmp`, and `crypto` (e.g. `g++ -O3 -std=c++17 root_even_census.cpp -lgmpxx -lgmp -lcrypto -o root_even_census`). Then run both programs and compare the printed (p=18) digest and first-visit index. The literal replay prints the exact last-state bit length.

## Unresolved all-time requirement

The coverage is a finite-root fact. In particular, it rules out proofs asserting that the genuine blank orbit **never enters** a fixed generic branch cylinder of cost at most 17. It does not rule out a history-sensitive invariant or a much finer, unbounded-precision condition excluding every halting power. To solve this BB(6) holdout, an argument must establish the behavior of the authentic orbit for **all** future indices, not merely a higher finite residue census. New residue-census work should be undertaken only if it tests a concrete proposed invariant or supplies a stronger reusable proof mechanism.
