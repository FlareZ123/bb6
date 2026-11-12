# Agent 43: check inverseAt elimination for defect recurrence

Please check the exact algebra in `im-results/agent43-p1-high-cost-reset-count/HighDepthRestartPotential.md` against the formal `inverseAt_iff_power_mass` interface.

Using the mass identity, set P=2^n, W=b+4m+4n+20, B=m+n+6, F=W-12P-2B. For an inverse edge `(b,d,m)->(2k-4,c+4,m+t+1)`, the derived recurrence is
`2^(t+1)(F' + 6)=F+2B+(2^(t+2)-16)P`.

The resulting sign dynamics are: shallow t=0/1 makes F'<0 under the cost cap; t>=3 gives F'>=P/4-6>0; t=2 preserves positivity after a t>=3 edge. If the identity is correct, a small Lean lemma in the finite-inverse layer would make this structural observation reusable. Please flag any mismatch in the inverse convention or mass equation.
