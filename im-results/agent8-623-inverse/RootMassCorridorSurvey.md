# Finite mass-corridor survey, n=10–20

**Status:** reproducible finite diagnostic, not a proof. The script `root_mass_corridor_survey.js` is a BigInt transcription of the pinned high-level recurrence. It starts at D(0,7), computes 100 section steps, and checks the near 7:4 and far 13:1 mass intervals using the bridge error (E_n=35n+120). The script should be cross-checked against Lean checkpoints before its outputs are treated as source-certified.

For scale (n), let (min[3^{n-1}-3,3^n-4]). The bridge ratios imply:
- near: (|4L-7m|le E_n), hence total mass in ([lceil(11m_{min}-E_n)/4ceil,lfloor(11m_{max}+E_n)/4floor]);
- far: (|L-13m|le E_n), hence total mass in ([14m_{min}-E_n,14m_{max}+E_n]).

The finite replay found that every root state whose mass lies in either corridor has ratio residual strictly larger than (E_n), for all scales 10 through 20. Selected minima:

| n | near indices | min near residual | far indices | min far residual |
|---:|---:|---:|---:|---:|
| 10 | 34–37 | 44,711 | 40–45 | 190,656 |
| 11 | 38–41 | 22,788 | 46–49 | 613,261 |
| 12 | 42–47 | 145,537 | 50–54 | 319,527 |
| 13 | 48–51 | 365,020 | 55–60 | 3,892,178 |
| 14 | 52–57 | 7,617,474 | 61–65 | 13,437,531 |
| 15 | 58–63 | 1,349,672 | 66–73 | 73,201,523 |
| 16 | 64–67 | 225,034 | 74–77 | 787,585,931 |
| 17 | 68–75 | 128,774,281 | 78–83 | 564,939,255 |
| 18 | 76–79 | 26,323,116 | 84–89 | 401,833,332 |
| 19 | 80–85 | 127,588,031 | 90–94 | 3,905,291,893 |
| 20 | 86–91 | 4,191,334,782 | 95–99 | 20,246,911,927 |

The smallest observed margin is n=11 near, residual 22,788 against E=505. No corridor intersection was observed.

## Research implication

This pattern supports a potentially general root-history invariant: blank-root visits may avoid both narrow predecessor ratio corridors, while monotone mass identifies only a short interval of root indices that needs checking at each scale. The n=10 proof draft in `RootMassGapAllN10.lean` formalizes the first instance once the extra checkpoints are source-verified.

Do not extrapolate the finite survey to all n. The long-term task is to prove a uniform lower bound on these ratio residuals, or a recurrence/invariant for the perturbed 3-Euclidean correction cocycle. Keep this in `im-results/`.


## Independent n=11/n=12 extension (Agent 48, 16 November 2026)

Agent 48 independently replayed the same pinned source transcription and identified the next two finite corridors. These remain candidate computation until their additional root checkpoints are verified against Lean:

- n=11 near: mass 162251–487269, bracketed by run37/run42; possible indices 38–41. Only run39 and run41 have min coordinate in the n=11 band, with residuals 22788 and 396018 (both > E=505).
- n=11 far: mass 826139–2480507, bracketed by run45/run50; possible indices 46–49. Only run47 has min coordinate in band, with residual 613261 (>505).
- n=12 near: mass 487011–1461586, bracketed by run41/run48; possible indices 42–47. Only runs44–46 have min coordinate in band, with residuals 145537, 1132662, and 696148 (all > E=540).
- n=12 far: mass 2479476–7440658, bracketed by run49/run55; possible indices 50–54. Only run52 has min coordinate in band, with residual 319527 (>540).

The additional candidate checkpoints required are run47–run55. Per Agent 48's recommendation, do not extend the Lean consumer until the current n=10 proof compiles cleanly.
