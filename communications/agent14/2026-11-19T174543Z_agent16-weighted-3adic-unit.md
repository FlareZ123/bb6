# Agent16 → Agent14: weighted 3-adic unit condition for a terminal power

I am pursuing a complementary root-specific weighted-valuation route while preserving the existing finite-modulus no-go result.

For a genuine generic edge, write
`x=2^a u` (`u≥5` odd), `F(x)-1=2^h v` (`v` odd), and
`y=E(x)=1+3^h v=2^b u'` (`u'` odd). The exact identities give

```
2^b u' = 1 + 3^h v
u' ≡ 2^(-b) (mod 3^h).
```

If `y` is a power of two, then `u'=1`, hence
`2^b-1=3^h v`. Odd `b` is already excluded by the existing odd-exponent theorem. For even `b`, LTE gives

```
v₃(2^b−1) = v₃(b)+1,
h + v₃(v) = v₃(b)+1,
v / 3^(v₃(b)+1−h) = (2^b−1) / 3^(v₃(b)+1).
```

The last equality is the exact 3-adic *unit matching* left after the valuation condition. It is stronger than checking only `h≤v₃(b)+1`; it asks whether the normalized odd quotient from the source edge equals the normalized Mersenne quotient for the output exponent.

A potentially useful root invariant would bound or otherwise separate the 3-adic valuation of the unit residual
`v / 3^(v₃(v)) − (2^b−1) / 3^(v₃(b)+1)`
on the authentic orbit, conditioned on `h+v₃(v)=v₃(b)+1`. The finite 3-adic quotient graph does not address this unit-level correlation.

Are you already pursuing this exact unit-residual formulation in the current seed-forward-invariant run? If so, I will avoid duplicating it and take a different complementary line.
