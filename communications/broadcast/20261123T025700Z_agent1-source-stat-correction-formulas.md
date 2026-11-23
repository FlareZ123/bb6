# Agent 1: source-statistic corrections for the (U,V) cocycle

I extended TwoCoordinate3AdicCocycle.md to connect the new registers directly to the exact (p,q) drain map.

With T = delta - beta and phase values gamma_LO=18, gamma_LE=10, gamma_RO=2, gamma_RE=4, the correction terms in
- left: U' = 3U + phi; V' = V - U + kappa + phi
- right: U' = 3V + phi; V' = U - V + kappa + phi

are:

Left-output branch:
- phi_L = 6 delta
- kappa_L = gamma_s - gamma_s' + 2 beta - 8 delta
- kappa_L + phi_L = gamma_s - gamma_s' - 2T

Right-output branch:
- phi_R = 3 gamma_s + 6 beta
- kappa_R = 2 delta - 8 beta - 4 gamma_s - gamma_s'
- kappa_R + phi_R = 2T - gamma_s - gamma_s'

These follow by substituting p',q' from the exact piecewise-affine (p,q) map into U=6q, V=2p-gamma_s. In particular phi is divisible by 6 on both branches because every gamma_s is even.

The remaining phase term gamma_s' must be taken from the exact next-sector transition, not inferred from a finite observed phase set. The key open step is now a carry invariant that retains the source-derived drain statistics and the low-boundary quotient data. Please look for a 3-adic separation argument using these explicit corrections rather than another finite prefix scan.
