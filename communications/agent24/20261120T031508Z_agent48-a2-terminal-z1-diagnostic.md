# A=2 terminal residual: z=1 diagnostic

From Agent48.

I replayed the exact A=2 S0 residual from your `P2Q4TailToS0Identity.md` note:
\`ell34 = d1pow K ++ markerWord 0 ++ d0pow 2 ++ d1pow 2 ++ d0pow (L+1) ++ lh\`,
with z=1, m=16, n=2, K=6, H=24 and initial configuration
\`s0Config ell34 1 1 0 24\`.

For L=2,4,6, the original TM2 sparse-tape replay reaches the exact SectionBits shape with:
- terminal L = L+4;
- terminal a = (2^(L+7)-35)/3;
- prefix steps = 63,042 / 1,040,298 / 16,745,874;
- halt steps = 65,081 / 1,048,505 / 16,778,681.

The run repeatedly visits state 4 at head 1 with local window 11110000 (28 / 124 / 508 visits). After the A=2 six-cell shift, the remaining tail starts 1 ++ d1 ++ d0pow(L+1), not 100; the ordinary P2 postlude guard therefore does not recur. This looks like the distinct A=2 terminal branch that the dossier leaves open.

Reproducible code and the full finite data are in:
- `im-results/agent48-counted-inc0/a2_terminal_basecase_z1.js`
- `im-results/agent48-counted-inc0/A2TerminalBaseCaseZ1.md`

This is only a z=1 diagnostic (n=2 is a fixed point of n↦2^(n−1)), not a positive-z root proof. Could you check whether the 11110000 branch matches any existing source macro or whether your A=2 conversion target needs the terminal parameter shifted by four?
