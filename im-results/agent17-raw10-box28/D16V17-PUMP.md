# D0=16, D1=17 final FAR holdout: two-counter nonhalting proof

The exact remaining row in job [140330042241](https://github.com/FlareZ123/bb6/actions/runs/45945785804/job/140330042241) is [8,10,11,22,11,13,16,17,20,4,0,12]. Sixteen other rows have preserved FAR candidates in artifact 15176513156. This row is now proved nonhalting in Lean using a modular invariant, locally compiled against the exact used C9Pair stream and Frontier/project definitions. The full repository import closure and complete cut consumer still need acceptance.

Let R(l,r) denote E reading one, with l ones to the left and r ones to the right, all remaining cells blank. Thus the scanned one is **not** counted in r. The blank execution reaches R(1,0) after six ordinary moves. The following exact positive return macros hold:

| condition | destination | ordinary moves |
|---|---|---:|
| r=0 | R(3,l) | 5l+8 |
| r=1, l>=2 | R(3,l) | 5l+4 |
| r=3 | R(l+2,0) | 6 |
| r=5 | R(l+5,0) | 15 |
| r>=7 | R(l+7,r-7) | 15 |

The two unbounded macros use a transfer section T(l,r) with right suffix 00 1^r. T(l+1,r) reaches T(l,r+1) in five moves; T(0,r) reaches R(3,r) in eight moves. All other macros are finite literal transition expansions, with arbitrary remaining unary suffixes.

Define Good(l,r) by either:
- l>=3, l=3 mod 7, and r mod 7 in {0,1,3,5}; or
- r=0 and l mod 7 in {1,5}.

Every Good root has a positive macro to another Good root: large r transfers seven ones, short r=0,1 returns to left count three, and r=3,5 gives the two exceptional l residues at r=0. R(1,0) is Good. Strong induction on arbitrary primitive execution length therefore proves the full infinite run, including positions inside each macro.

Lean 4.36.0-rc2 local preflight: Box28D16V17Pump.never_blank and Box28D16V17PumpSource.compatible_never both compiled, with only propext, Classical.choice, Quot.sound. The latter uses the literal full machine table and the existing project_applyMove correspondence. The local compilation used the verbatim relevant definitions in reduced dependency modules because direct Git checkout is unavailable (DNS); this is not a claim of full source-closure acceptance.

The D16V17 emitter may consume the new theorem after CI. Do not repeat FAR search on this row or the 16 already solved rows. D16V18 has a distinct unsolved row [8,1,11,0,11,13,16,18,10,22,23,4]. No complete D0=16 bound or global Cover is claimed.
