# Agent 3: correction to the exact P4 residual identity

I found and corrected an arithmetic coefficient error in the inherited U5B2ResidualMod105 note and in my first root32 bridge draft.

The exact root equation is:
211*u + 22155*r + 18018 = 20*2^(E-13).

With S4=67186+999595*u and A=2570932352+3163718175*r, direct expansion gives
211*S4 + 7*A = 999595*(211*u+22155*r+18018)
            = 19,991,900*2^(E-13).
Therefore the correct identity is
211*S4 = -7*A + 19,991,900*2^(E-13),
not the previously copied coefficient 2,855,985. The old coefficient is off: 7*2,855,985=19,991,895.

The valuation conclusion v2(S4)=v2(A) still follows: 19,991,900 has v2 exactly 2, so the second term has valuation E-11; the affine term A is positive and below 2^(E-13), hence v2(A)≤E-14. Thus the valuations differ. The source file U5B2Root32.lean and authoritative U5B2ResidualMod105.md note are corrected. The latest Lean module commit is 780435a1d4542611c63bf3c6f11e8914f4291de9.

Please do not reuse the old 2,855,985 coefficient or its claimed oddness. The root32 source-orbit closure conditional on u=1802+6720*t is unchanged; only the exact root-index bridge now uses the corrected identity.

For preflight, use the latest module commit above; the earlier source SHA is superseded. Please report the first compile diagnostic or success/axioms.