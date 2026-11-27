# F197: exact parametric reset-section rewrites

This is a new symbolic reduction, not a nonhalting decision. Uses the exact grouped run map in [RunSection.md](RunSection.md). Write (B(L,W)) for the B section with left run word (L), shortened right tail (0W); (D(L,z,Y)) for D with left tape (0L), right (z) leading zeroes followed by (Y). A run symbol ((a,g)) means (a) ones followed by (g) zeroes; (g=0) denotes the terminal implicit blank tail. All suffixes below are nonempty well-formed left run words. Define

- (A=(1,1)), (J=(1,2)), (T=(2,2)), (C=(2,1)), (U=(3,2));
- (P=AAT), (e=(1,0)), (d=(2,0));
- right symbols (x=(1,1)), (y=(2,1)), (s=(5,3)), (t=(3,3)), (u=(4,3)).
- (I(W)) increments the first right run; (Q(W)=uI(W)).

## Lemma 1: arbitrary repeated prefix consumption

For every well-formed (X), nonblank (W), and (ngeq 0),

[
B(P^n X,W) \longrightarrow^{*} B(X,Q^n(W)).
]

The path for one (P) is
[
 B(AATX,W)\to D(TX,0,(2,3)W)
 \to D(AUX,2,W)
 \to B(AUX,I(W))
 \to B(X,uI(W)).
]
These are B F-exit, D110, D00, B F-loop, respectively. Each path is safe and costs exactly 36 live transitions (8+13+6+9), four grouped steps. Induct on (n). In particular
[
Q^0(e)=e,\qquad Q^{n+1}(e)=u s^n d.
]
No simulation bound is involved.

## Lemma 2: exact decoder

For every (kgeq 0) and (V),

[
 B(JV,x s^k d)\longrightarrow^{*} B(P^{k+1}V,e).
]
Start with B J (odd gap2), then D1000, D1011:
[
B(JV,xs^kd)\to D(V,0,(1,3)xs^kd)
\to D(TV,0,xs^kd).
]
For (k=0), D1011 consumes (x d), yielding (D(PV,0,\epsilon)), then blank reversal yields (B(PV,e)). Cost 7+4+10+6=27. For (k>0), D1011 consumes (x) and two ones of (s), leaving (D(PV,0,t s^{k-1}d)). D111 pushes (J), D00 at leading gap3 prepends (x) to the remaining right word, giving (B(JPV,xs^{k-1}d)). Cost 7+4+10+5+6=32. Induction yields total (32k+27) live transitions, (5k+4) grouped steps.

## Theorem: two infinite families of reset rewrites

For all (ngeq0), nonempty well-formed (X),
[
\boxed{B(P^n AAA X,e)\longrightarrow^{68n+74}B(P^{n+1}X,e)}
]
and
[
\boxed{B(P^n TAA X,e)\longrightarrow^{68n+88}B(P^n AAAT X,e)}.
]
All intermediate steps are defined (nonhalting), and these are first positive returns to (W=e). Grouped step counts are (9n+10) and (9n+12), respectively.

**First proof.** Apply Lemma 1 to obtain (B(AAA X,W)), (W=Q^n(e)). The next six grouped steps are:
[
B(AAA X,W)\to D(AX,0,(2,3)W)
\to D(ACX,2,W)\to B(ACX,I(W))
\to D(X,0,tI(W))\to D(JX,3,I(W))
\to B(JX,xI(W)).
]
Costs 8+13+6+9+5+6=47. For all (n), (I(Q^n(e))=s^n d). Lemma 2 gives (B(P^{n+1}X,e)), total (36n+47+32n+27=68n+74).

**Second proof.** After Lemma 1, B even on (T) replaces it by (A), prepending (x) to (W) (10 live). Apply the same six-step middle, with (xW) in place of (W), to obtain (B(JX,xyW)). The J/D1000/D1011 path leaves (D(PX,1,W)), cost 21. D01 consumes one of (W)'s first run and pushes (A). If (n=0), this is blank, so D00 gives (B(APX,e)). If (n>0), the first run (u) becomes (t); D111 and D00 give (B(JAPX,xs^{n-1}d)). Lemma 2 yields (B(P^n APX,e)). Total cost in both cases (68n+88). Here (AP=AAAT).

## Further exact local reset rules
For all (X), (B(JX,e)\to^*B(TTX,e)) (4 grouped steps), and (B(AUJX,e)\to^*B(TTJT X,e)) (7 grouped steps). Both follow by directly expanding the run map. They are not needed for the two theorems.

## Why this matters
The actual reset-section orbit has very long (P)-prefixes. An instrumented first 5,000 returns (starting at (B((2,0),e))) extracted 1,960 distinct literal prefix rewrites; a substantial fraction touched 1,024+ input runs, but many are the above families with large (n). The parametric identities replace arbitrarily long sweep segments by exact prefix rewrites. They are proved for arbitrary suffixes, not inferred solely from those experiments.

Open: characterize the remaining suffix cases at the end of a maximal (P)-prefix, and prove a closed reset-section grammar. The two families alone do **not** imply a decision of F197. The observed adjacent-factor grammar over (A,J,T,C,U,e) is not inductive: e.g. input (ACA CA A e) (run list [2,5,2,5,2,2,1]) reaches an unsafe B entry; the actual orbit may exclude it. This is an obstruction to that candidate grammar, not an actual blank-orbit halt.
