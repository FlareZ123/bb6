# Sheep: two exact direct power-parent gates at unbounded 3-adic depth

**Agent 40, 9 November 2026. Intermediate all-integer mathematical result.** For the authentic first-even Sheep return, two direct incoming source sectors have exact, elementary, **uniform-in-the-3-adic-depth** necessary and sufficient conditions. Unlike fixed-stratum modular sieves, the parameter n below is unbounded. This provides explicit genuine inverse edges (or their absence within these two sectors) even at the high-valuation tail `n>=17` left open by the finite-stratum sieve in [Agent14's 2026-11-09 dossier](../agent14-sheep-v3-split/README.md). It is *not* a full predecessor classification, a proof of new all-power exclusions, a Sheep halting decision, or a BB(6) bound.

The standard six-state Sheep machine is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Agent16 already connected its genuine blank computation, whose first-even input is 10, to the authentic first-even section transition in [original-source Lean CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

## Uniform depth family

Let `n>=1`, `t>=1`, `3∤t`, and `j=8*3^n*t`. The target is `Y=2^j`. Set `d=3^(n+1)` and `u=(2^j-1)/d`. Then

\[
\boxed{2^{8\cdot3^n}\equiv1+3^{n+1}\pmod{3^{n+3}}}\quad(n\ge1),
\tag{1}
\]

\[
\boxed{2^{8\cdot3^nt}\equiv1+t3^{n+1}\pmod{3^{n+3}}},\quad
\boxed{u\equiv t\pmod9},\quad v_3(2^j-1)=n+1.
\tag{2}
\]

**Proof of (1):** Base `n=1`: `2^24 mod 81=10`. Suppose `X=2^(8*3^n)=1+A+9Az` with `A=3^(n+1)` divisible by nine. Write `X=1+Aw`, `w≡1 mod9`. Expanding `X^3=1+3Aw+3A²w²+A³w³` modulo `27A=3^(n+4)`, the last two terms vanish because `9|A`, and the first is `1+3A`, proving induction. For (2), raise (1) to the power t; the binomial remainder of degree ≥2 is divisible by `A²`, hence by `9A`, since `9|A`. The exact 3-valuation follows from `u≡t mod9` and `3∤t`. This proof applies at arbitrarily large n without enumerating any finite list of strata.

## Gate A: exact a=2 section parents for every n

The authentic generic even source `x=4v` with odd `v>=5` has
`F(x)=(9v+3)/2` and `F(x)-1=(9v+1)/2`. If `E(x)=Y`, then `3^h|(Y-1)` and necessarily `h=n+1`: the equation `9v+1=2^(h+1)(Y-1)/3^h` has left side coprime to three. Therefore a legal generic first-even source with **2-valuation exactly two** exists if and only if

\[
\boxed{2^{n+2}t\equiv1\pmod9}.
\tag{3}
\]

When (3) holds, this source is unique:

\[
\boxed{x_2(n,t)=
4\left(\frac{2^{n+2}(2^{8\cdot3^nt}-1)/3^{n+1}-1}{9}\right)}.
\tag{4}
\]

The inner quotient is an odd integer at least five: its numerator is odd, division by nine preserves oddness, and `j>=24` ensures its size. Reversing the F identity gives `F(x_2)-1=2^(n+1)u` with `u` odd, hence the hidden odd-run length is exactly n+1 and `E(x_2)=Y`. Necessity follows by reversing the same equation and invoking (2). Thus (3) is an actual original-source-matched **iff for all a=2 parents**, with no hidden upper bound on n. The residue on t repeats every six n-levels because 2 has multiplicative order six modulo nine:

| n mod 6 | t mod 9 required |
|---:|---:|
| 0 | 7 |
| 1 | 8 |
| 2 | 4 |
| 3 | 2 |
| 4 | 1 |
| 5 | 5 |

As a check on shared research, Agent14's formerly fixed `n=7` / h8,a2 row requires t mod9=8, precisely the n mod6=1 case here. The uniform proof covers arbitrary n, including n≥17, **without** asserting what other predecessor sectors do.

## Gate B: exact (a,h)=(6,3) section parents for every n≥3

For `n>=3` and **any** `t>=1` (even when divisible by three), set `j=8*3^n*t`. An incoming genuine generic edge with source valuation `a=6` and hidden odd-block length `h=3` exists if and only if

\[
\boxed{4\cdot3^nt\equiv5\pmod7}.
\tag{5}
\]

When the congruence holds, the unique such source is

\[
\boxed{x_{6,3}(n,t)=
64\left(\frac{2^{j+4}-259}{3483}\right)}.
\tag{6}
\]

**Proof:** The exact generic inverse equation for this pair is
`3483*v+259=2^(j+4)`, and `3483=81*43`. Since `54|j` for n≥3, `2^(j+4)≡16≡259 mod81`. Modulo 43, `259≡1`, and `ord_43(2)=14` (verify `2^7≡-1 mod43` and `2^2,2^7≠1`). Thus the remaining condition is `14 | j+4`, equivalent to (5). The resulting cofactor v is an odd integer at least five for n≥3; substituting back proves `F(x)-1=8*(2^j-1)/27`, with odd quotient, and exactly h=3 hidden steps ending at `Y`. Distinct congruence failures leave no legal source **in this one (a,h) sector**.

The allowed t residue modulo seven repeats with n modulo six:
`n mod6 = 0,1,2,3,4,5` gives `t mod7 = 3,1,5,4,6,2`, respectively.

## Evidence, scope and direct research use

[verify.py](verify.py) uses exact integer/modular arithmetic, checks (1)-(6) through 64 unbounded-parameter sample depths, 22 t inputs each, and independently reconstructs the full genuine even return from representative source integers. The mathematical proofs above are induction and exact source algebra; finite test coverage is **supplementary**. The new unbounded claims have **not** been freshly compiled into a single new original-Turing-machine Lean theorem. The authentic machine-to-section equations are already certified by Agent16, while the general finite-stratum method and overlap are described by Agent14.

The earlier all-t [Agent40 three-parent classification for j=648t, 3∤t](../agent40-sheep-648-parents/README.md) is the special depth n=4 with additional exhaustive analysis of every other possible (a,h) valuation. That theorem excludes 132 actual halting-power exponent residues modulo204120. The present all-n result gives exact **partial** inverse sectors, including much higher n, and makes **no additional complete-root exclusion claim**.

A promising next line is to combine the uniform gates with an all-depth bound on the **other** `(a,h)` sectors or a history-sensitive invariant on the unique blank orbit starting at 10. Higher inverse-depth corridor constructions for n≥17 are another possible application. No theorem here settles Sheep or the exact BB(6) function.
