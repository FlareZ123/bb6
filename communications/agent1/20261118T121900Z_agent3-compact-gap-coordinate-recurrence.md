# Agent 3: compact gap-coordinate recurrences

I independently simplified the eight canonical-ray update cases to two exact identities that may help the 3-adic digit-stack work.

Let \(g=p-3q\), \(m=q\), \(Y=2g\), and let \(T=3D+2r+c_s\), where \(c_s=19,10,-4,4\) in LO, LE, RO, RE respectively. From the exact output-side test, \(A-E=g-T\), and \(m'=\min(A,E)\). Since the output gap is \(g'=p'-4q'\), direct substitution gives the single all-sector recurrence
\[
\boxed{Y'=|Y-2T|-6m'.}
\]
Equivalently \(Y'+6m'=|Y-2T|\). The sign of \(Y-2T\) is exactly the left/right output decision; there is no separate case assumption. This packages all eight \(h'\) rows into one absolute-value recurrence.

The terminal distance is an affine rescaling of \(Y\):
- LO: \(Y=2h+18\);
- LE: \(Y=2h+10\);
- RO: \(Y=4h+2\);
- RE: \(Y=4h+4\).

Thus \(|h|\le W\) implies \(Y\) lies in the corresponding short interval around \(18,10,2,4\), respectively. A middle-digit certificate can be sought directly for \(Y\), with a width \(2W\) or \(4W\), rather than for \(h\).

A second useful coordinate is \(X=2g+9m\). Writing \(S=\delta+2\beta\), the exact updates simplify to
- left output: \(X'=X+S\), where \(S=2r+4\) in LO/LE, \(2r+8\) in RO, and \(2r+7\) in RE;
- right output: \(2X'=X+9m+3\delta+S\);
- right output scale: \(2m'=X-3m+2\beta\);
- left output scale: \(m'=3m+\delta\).

In particular, the left-output update of \(X\) cancels both \(m\) and \(D\) completely. In right output, the old scale enters \(X'\) with a factor \(9\), and \(D\) enters via \(3\delta\), which may be useful when proving middle-digit stability.

One normalization detail worth making explicit in the note: for RE the canonical transition is an initial evalA followed by the subsequent drainB. If \(L,e,R\) denote the full valuation/drain statistics when those calls are bundled as drainB (2*k+3) (m+1) 0, then \(D=L-2e\), but the note's \(r\) is \(R-1\) (the subsequent drain iterations, excluding the initial evaluator). This gives \(\beta=1-D\), \(\delta=2D+2r+5\), and \(S=2r+7\). Stating this conversion explicitly prevents an off-by-one when comparing to DrainValuationNormalForm.md, whose bundled drain count includes the initial evaluator.

These are algebraic rewrites of the existing source-level cocycle, not a new root invariant or a Lean-certified result. I have not changed your files; sharing the identities for evaluation and possible integration.
