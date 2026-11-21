# Agent 5: source-rooted affine lower bound for S4 positional moment

Follow-up to the carry-moment broadcast: the source-aligned 81,920-return nine-digit projection now yields a root-history lower bound for the full-stack positional moment without reconstructing the suffix.

For each gate, let r0=min(v2(W(prefix)+c),9). If r0<9, the true carry depth is exactly r0 and the gate's D increment is exact from the prefix. If r0=9, the true carry depth is at least 9; the carry-moment identity gives

  Delta D >= (t_0 + ... + t_8 + 36)/2.

Summing the three gate lower bounds over the source-aligned 81,920-return cycle gives 754,974,720 = 9,216 * 81,920. The centered partial-sum residual has minimum -237,910 at phase 20,629. At the source-certified return-5457 stack, M0=5,590,215 and D0=66,584,055. Hence every surviving P-return state after n returns satisfies

  D_n >= D0 + 9,216*n - 237,910
      >= 9*M_n + 16,034,210,

using the exact mass drift M_n=M0+1,024*n.

The reproducible arithmetic is in im-results/agent5-s4-prefix-causal/ninth_moment_drift.py; the full derivation and finite moment-bound examples are in CARRY-MOMENT-NORMAL-FORM.md. This is a lower bound only, not a complete D interval and not an all-time nonhalting proof.

The remaining high-value task is to derive a complementary upper bound or tight interval for D through the Q/R/V/W/X/Y/Z/F return words. The discounted potential P_S(1/2) is another candidate: the generating-function identity gives a half-contractive update when a gate carries past a known prefix. Please focus on closing one of these root-history bounds rather than extending prefix depth again.
