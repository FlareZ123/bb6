# Algebraic generating function and sharp asymptotics of #623 B-drain survival counts

**Status.** This is a paper-level derivation based on the exact source-certified `flatB_eq_drainB` recurrence from [Agent 49](../agent49-parity623/FlatDrainSource.lean) and the independently derived exact cardinality recurrences in [this directory](README.md). The new analytic formulas are not yet Lean kernel formalizations. They count all *synthetic* B-block inputs with fixed initial first counter; the authentic `D(0,7)` orbit is still unclassified.

## Algebraic generating function

Set `S_a(n)=#{0≤b<3^n: drainB a b d succeeds}`, independent of `d`, and write the ordinary generating function `F_a(z)=sum_{n≥0} S_a(n)z^n`. The exact recurrences in [README](README.md) imply the following **formal power-series** identities:

```text
F_0 = 1/(1-z²) + z(F_0+F_1)
F_1 = 1-z/(1-z²) + z(F_2+2F_0)
F_a = 1 + z(F_(a+1)+2F_(a-1)),  a≥2.
```

For `|z|<1/3`, the bound `0≤S_a(n)≤3^n` is uniform in `a`, so `F_a` remains bounded as `a→∞`. Define

```text
Q(z) = sqrt(1-8z²),  Q(0)=1,
R(z) = (1-Q(z))/(2z),  R(0)=0,
P(z) = 1/(1-3z).
```

The last recurrence has characteristic equation `z r²-r+2z=0` and constant particular solution `P`. The other root `(1+Q)/(2z)` diverges for small positive `z`, so its coefficient vanishes under the uniform-in-`a` bound. Consequently `F_a=P+(F_1-P)R^(a-1)` for every `a≥1`. Substitute `F_2=P+R(F_1-P)` into the first two equations and solve for `F_0`. The exact resulting generating function is

```text
                  z(1+Q-4z)/(1-3z) + (1+Q-2z²)/(1-z²)
F_0(z) = ----------------------------------------------------------
                    (1-z)(1+Q) - 4z².
```

The apparent singularity at `z=1/3` is removable: `Q(1/3)=1/3`, and its numerator factor `1+Q-4z` vanishes there. In particular, the dominant singularity radius is `R_*=1/sqrt(8)=1/(2sqrt(2))`.

A direct coefficient expansion confirms the exact initial recurrence values:

```text
F_0(z) = 1 + 2z + 5z² + 12z³ + 29z⁴ + 76z⁵
           + 189z⁶ + 508z⁷ + 1293z⁸ + 3508z⁹
           + 9069z¹⁰ + 24732z¹¹ + 64637z¹² + ...
```

## Theorem: sharp two-parity first-order asymptotics

As `n→∞`, the exact surviving counts satisfy

```text
S_0(n) = (2sqrt(2))^n / n^(3/2) *
         [ C_+ + (-1)^n C_- + O(1/n) ],

C_+ = (324 + 228sqrt(2))/(7sqrt(pi)),
C_- = (228sqrt(2) - 324)/(7sqrt(pi)).
```

Equivalently, separated by parity,

```text
S_0(n) ~ (2sqrt(2))^n / n^(3/2) *
           { 456sqrt(2)/(7sqrt(pi)), n even,
             648/(7sqrt(pi)),        n odd. }
```

The corresponding fraction of successful block inputs `b<3^n` is asymptotically proportional to `(2sqrt(2)/3)^n n^(-3/2)`. This sharpens the explicit geometric upper bound `(17/18)^n` proved in the parent note and identifies its optimal exponential base for `a=0`. The even and odd constants are approximately `51.9764799609` and `52.2278357341`, respectively.

**Singularity proof.** With `Q` treated as an auxiliary variable, write the numerator and denominator of `F_0` as `N_0(z)+N_1(z)Q` and `D_0(z)+D_1(z)Q`, where

```text
N_0 = z(1-4z)/(1-3z) + (1-2z²)/(1-z²)
N_1 = z/(1-3z) + 1/(1-z²)
D_0 = 1-z-4z²
D_1 = 1-z.
```

At either branch point `z=±R_*`, the coefficient multiplying `Q` in the local expansion of `F_0` is

```text
A(z) = [N_1 D_0 - N_0 D_1]/D_0²
     = 2z²(4z²-3z+1) /
         [(z-1)(3z-1)(4z²+z-1)²].
```

Direct exact evaluation gives

```text
A(+R_*) = -(456+324sqrt(2))/7,
A(-R_*) = (-456+324sqrt(2))/7.
```

Near `z=R_*`, `Q(z)=sqrt(2)*sqrt(1-z/R_*)*(1+O(1-z/R_*))`. Near `z=-R_*`, replace `1-z/R_*` by `1+z/R_*`. At `z=±R_*`, the denominator of `F_0` is `1/2∓R_*`, strictly nonzero. There are no additional singularities on the circle: any zero of `(1-z)(1+Q)-4z²`, after squaring the equation for `Q`, would force `z=0` or `z=1/3`; direct substitution shows the denominator is nonzero at both points on the branch analytic at the origin. The factors `1-z²` are also nonzero inside this circle, and the apparent `1-3z` singularity cancels.

The standard square-root coefficient transfer `[z^n]sqrt(1-z/R_*) ~ -R_*^(-n)/(2sqrt(pi)*n^(3/2))` now yields the two branch-point contributions, with `(-1)^n` from the negative singularity. Their sum is the stated asymptotic, and the next local half-integer power supplies the `O(1/n)` relative correction. This uses ordinary analytic-combinatorics singularity transfer, rather than a formal Lean proof of asymptotic analysis.

## Reproducibility and limits

The [integer recurrence checker](verify_counts.py) produces all exact counts efficiently and validates the finite coefficients. A separate symbolic expansion with exact algebraic `Q=sqrt(1-8z²)` confirmed the generating series through `z¹²`. Integer recurrence values at `n=120,200,500,1200` gave respectively `36.7368,41.4835,47.1084,49.8083` for the normalized even factor `n^(3/2)S_0(n)/(2sqrt(2))^n`, trending toward the predicted `51.97648`. These numerical checks support the algebra; the proof follows from the exact recurrence and the displayed analytic identities.

The fixed-`a` success-density result is compatible with infinitely many exceptional successful ternary inputs and says nothing about how the single authentic blank-root machine samples those inputs. It supplies a quantitative inverse-enumeration tool, not a decision of #623 or BB(6). Before treating this as externally publishable, compare with established exact lattice-path/Catalan generating-function results; prior work in Agent 49 is correctly credited for the underlying source recursion.
