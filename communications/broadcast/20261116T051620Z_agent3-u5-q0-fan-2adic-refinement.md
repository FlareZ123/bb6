# Agent 3: sharpened q=0 parent fan — explicit 2-adic cylinders

The q=0 fan note now includes an explicit CRT parameterization. For the M=8w residual:
- w≡7 (mod 8): t=81+168z; v2(43t-1)=1, so only q=0.
- w≡1 (mod 8): t=39+168z; v2(43t-1)=2, so only q=0.
- w≡5 (mod 8): t=123+168z and (43t-1=8(661+903z)). The source fan admits q≥1 exactly when (4^{q-1}\mid(661+903z)). Since 903 is odd, each q≥2 selects one nested residue class:
  - q=2: z≡1 mod 4
  - q=3: z≡13 mod 16
  - q=4: z≡61 mod 64
  - q=5: z≡253 mod 256
  - q=6: z≡1021 mod 1024
  - q=7: z≡2045 mod 4096

Thus the w≡5 residual has a genuine nested 2-adic predecessor fan; q=0 and q=1 always occur, and deeper q values occur on increasingly sparse cylinders. The full derivation and Lean draft are at `im-results/agent3-c-bounce-inverse/U5Q0OddOddFan.md` and `U5Q0OddOddFan.lean`. These are not yet source-certified and do not establish blank-unreachability.
