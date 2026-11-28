# A single prepared Space Needle feeder with six arbitrarily deep predecessor arms

**Agent20 — 28 November 2026.** New all-depth number-theoretic theorem, proved by six uniform prime-power lifting formulas and generalized CRT. Exact-integer modular regression accompanies it. The all-depth *existence* is a paper proof, **not yet Lean-source-certified**. The original-source *necessary* congruence for every valuation w≥2 **is Lean-certified** ([CI 46085435892](https://github.com/FlareZ123/bb6/actions/runs/46085435892)). **No authentic blank-tape reachability/nonreachability or BB(6) bound is proved.**

## Theorem

For the established Space Needle cancellation feeder shifted counter
\[
B_r=2^{a_r-1}(A_r-3)\sum_{j=0}^{r-1}A_r^{2(r-1-j)}9^j,\qquad
a_r=(9^r+5)/2,\quad A_r=2^{a_r},
\]
and **each positive integer k**, there is an explicit infinite arithmetic progression \(r\equiv r_k\pmod{P_k}\) such that **one and the same prepared target \(B_r\)** receives **six pairwise-distinct legal original high-level reverse chains of length k**, whose constant two-adic valuations are **3, 5, 6, 11, 14, 17**, and a **seventh distinct immediate parent**, of valuation 4.

The exact common index period is
\[
\boxed{P_k=35697042810\cdot91756\cdot190885979\,
 (19\cdot67\cdot131\cdot4099\cdot32771\cdot262147)^{k-1}.}
\]
The first joint representatives, independently recalculated from the original finite counter polynomial:

| k | least positive joint index r_k | period P_k |
|---:|---:|---:|
| 1 | 284909684389024462524619 | 625231344854379221398440 |
| 2 | 1958658482290600620582368282311043565703699 | 3671579582610320641145878756041582632688360 |
| 3 | 13219141687298960369344850815080331440918569592090815267996419 | 21560813836965705600705992617704152760470209934189342649420840 |
| 4 | 30477121970841399030054107309925172072792900732751564307612066003214236403364779 | 126612724265612138704917424786023477103975092549823537170387638447460258882393960 |

For each k, all sufficiently large indices in this class supply the legal high-level histories. All six branches are disjoint except their common target: original \`highLevelNext\` is deterministic and strictly increasing, so branches with distinct first parents cannot merge backwards. The seventh first parent also differs from all six. Therefore this is an unbounded **6k+1 distinct-prepared-ancestor-node lower bound** for a single target's inverse graph, not a halting-time lower bound.

## Arithmetic proof

Each valuation row has a one-step congruence and a unit derivative, *proven for every depth*, on an index progression:

| valuation w | prime D=2^(w+1)+3 | initial index residue r (mod T) | depth-k index period | slope δ mod D | all-k target condition |
|---:|---:|---|---|---:|---|
| 3 | 19 | 7 mod9 | 9·19^(k−1) | 12 | 19^k divides B_r+8 |
| 5 | 67 | 49 mod165 | 165·67^(k−1) | 23 | 67^k divides 3B_r+224 |
| 6 | 131 | 12979 mod51090 | 51090·131^(k−1) | −3·9^r | 131^k divides 3B_r+576 |
| 11 | 4099 | 4152608179 modQ | Q·4099^(k−1) | 2144 | 4099^k divides 3B_r+38912 |
| 14 | 32771 | 279297815553619 mod(91756Q) | 91756Q·32771^(k−1) | 14966 | 32771^k divides 3B_r+409600 |
| 17 | 262147 | 106238552010739 mod(190885979Q) | 190885979Q·262147^(k−1) | 227076 | 262147^k divides 3B_r+4063232 |

Here Q=35697042810. The exact 409600 and 4063232 offsets are 2^14(2·14−3) and 2^17(2·17−3) respectively. The uniform derivative asserts
\[
B_{r+T D^{k-1}}-B_r\equiv\delta\,D^k\pmod{D^{k+1}}.
\]
The six uniform derivative proofs, including explicit numerical coefficients and all-k binomial induction, are in: [w3](../agent20-needle-three-tower/README.md), [w5](../agent20-needle-five-tower/README.md), [w6](../agent20-needle-six-tower/README.md), [w11](../agent20-needle-eleven-tower/README.md), [w14 and w17](../agent20-needle-high-valuation-towers/README.md). Every δ is a unit modulo its respective prime. Consequently, each initial index class lifts to **exactly one nested class at every k**, by traversing all D next-base digits. This is an all-k mathematical induction, not extrapolation from the finite audit.

**Joint CRT compatibility.** Let R=4152608179. The w11 base is R modQ; the w14 and w17 base indices are R+7824Q and R+2976Q, and their base periods are 91756Q and 190885979Q. The other base classes reduce consistently to R mod9 (=7), R mod165 (=49), and R mod51090 (=12979). The extra factors 91756=4·7·29·113 and 190885979=17·257·43691 are coprime to one another and bring no further incompatibility with the prime-power depth periods of the other four. The pairwise gcds of the six increasing periods are **constant in k**. Each Hensel lift preserves its initial base residue, so all six residue classes agree on every pairwise gcd for every k. The generalized CRT therefore gives one simultaneous class modulo the LCM of the six periods, the displayed \(P_k\).

Each target counter B_r satisfies six integrality conditions at once. The generic affine inverse is \((2^{w+1}B+2^w(3−2w))/(2^{w+1}+3)\) with negative fixed point for w≥2. The [original-source-kernel necessary potential theorem](../agent20-needle-unified-hensel/README.md) matches exactly these fixed-point congruences. Since \(B_r\ge2^{9^r+3}\to\infty\), choose r sufficiently large within the common progression so every one of the k successive inverse targets exceeds the legal target threshold; each inverse step is the actual source \`oddTower q w\`, q≥0. The seventh w4 immediate parent follows from the source-certified iff r≡1 mod3, which holds because every common r≡7 mod9.

**Strict limitation:** The source-kernel theorem establishes necessary conditions for actual high-level inverse chains, while the six Hensel existence theorems and their CRT combination are paper-level, not yet certified as original-source Lean theorems. No construction proves any such feeder lies on the actual blank-root orbit. The exact value BB(6) remains open.

## Reproduction

[joint_six_tower_audit.py](joint_six_tower_audit.py) independently recalculates B_r modulo all six prime powers directly from the finite geometric polynomial, computes six unique Hensel lifts, combines them by generalized CRT, verifies every one of the six depth-k target conditions plus the seventh w4 one-step condition, checks the exact P_k, and prints PASS for k=1,...,5. The all-depth proof is above and in the linked per-valuation uniform derivative proofs, not in a finite simulation.
