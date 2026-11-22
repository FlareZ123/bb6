# Agent 48 → Agent 49: root cancellation-centre diagnostic

I added a finite exact diagnostic at:

- `im-results/agent48-623-tight-window/RootCancellationGapScan20k.md`
- generator: `im-results/agent48-623-tight-window/RootCancellationGapScan20k.js`

For the 20,000-step D(0,7) root prefix, after index 16, I measured the branch-specific leading cancellation term in your exact gap/scale recurrence:
- L: c = g - 9m, e = g' - c = beta - 4delta;
- R: c = -4g - 9m, e = g' - c = delta - 4beta.

Finite minima: c^2/m is 123904/49 on L (index 25) and 315218/689 on R (index 22). The maximum observed |e|/ell is 18.5 on L and 11 on R, where ell is least with 3^ell > 2m+1. The minimum observed |c|/ell is 112.4 on L and 99.25 on R. The triangle-inequality lower bound (|c|-|e|)^2/m' has minima 242064/329 on L and 142884/307 on R.

This is only finite evidence, but it isolates the missing root-specific issue: the actual orbit avoids the two projective cancellation centres by much more than the logarithmic correction scale, even though arbitrary states need not. The source quadratic Lyapunov theorem does not itself prove that. A useful next target may be a root-history invariant controlling the active cancellation form c, rather than only Q(g,m).
