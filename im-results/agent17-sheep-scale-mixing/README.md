# Sheep: finite logarithmic-phase and residue invariants are eventually cofinite

**Agent 17, 24 November 2026.** This intermediate structural theorem extends the prior univariate Presburger obstruction to bounded leading digits, fixed congruences, and periodic digit-length phases. The full argument is a mathematical proof using Agent22's all-modulus quotient connectivity. The discrete progression-lift and corridor lemmas in the companion Lean module were locally kernel checked against the exact repository Sheep section model; the real-logarithm composition and connectivity theorem remain paper-level. No Sheep blank-root decision or BB(6) bound follows.

## Theorem

Let m be any positive even integer and P any positive real number. For positive x write phi(x)=log_2(x) modulo P on the circle [0,P). Partition this circle into finitely many half-open intervals of positive length. Suppose I is an infinite set of positive even integers, and above a fixed threshold membership in I depends only on (x mod m, the interval containing phi(x)). If I is closed under every genuine generic first-even Sheep edge from an element of I, then I contains **all sufficiently large even integers**.

Consequently no such invariant can contain the authentic initial even section 10, be inductive under all defined nonterminal edges, and exclude all powers of two. If it did, the genuine strictly increasing orbit would continue forever in I, making I infinite and contradicting the theorem.

This covers fixed leading binary bits with arbitrary fixed congruences and bit length modulo any integer (take P equal to that integer). More generally it covers bounded leading digits in any single base b>1 and digit length modulo a fixed integer (take P to be that integer times log_2(b)). Finite combinations with a common logarithmic period admit a common refinement. Odd moduli may be doubled to incorporate parity. The theorem does not cover arbitrary regular languages of entire digit strings, growing precision, incommensurable phase combinations, or unbounded root histories.

## Exact source and discrete ingredients

The original machine is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. At even x=2^a u with a>=1, odd u>=5, F(x)=x+a+(u-1)/2. Factoring F(x)-1=2^h v with v odd, the genuine first-even edge is E(x)=1+3^h v. The u=3 exception is not needed. The [original-source bridge](../agent16-sheep-even-return/README.md), CI 41505950547, proves raw halting iff an even path from 10 reaches 2^j for some j>=2.

### 1. Every generic residue edge admits an arithmetic-progression lift

Fix a generic even edge x0->y0 with parameters a,h,u,v. Set L=2^(a+h+1), N=3^h(2^(a+1)+1). For every even d>=0,

    x(d)=x0+L*d,    y(d)=y0+N*d

is a genuine edge with the same a,h. Replace u by u+2^(h+1)d and v by v+(2^(a+1)+1)d. Positivity and oddness persist; the change in F is 2^h(2^(a+1)+1)d. Taking d=m*t preserves both residues and yields unbounded arithmetic progressions for both endpoints.

The Lean theorem `generic_lift` proves the h+1 exact section steps in the unmodified SheepEven.Step/Steps model. For a>=1, the shifted endpoints are even and the h intervening odd steps are the maximal odd block, so this is a genuine first-even edge.

### 2. Two exact logarithmic rotations

For even v>=14 and k>=1, both sequences below are genuine paths, each arrow one generic even return:

    x_i=4^(k-i)*5^i*v-2,    0<=i<=k,
    z_i=8^(k-i)*9^i*v-12,   0<=i<=k.

Indeed the respective single arrows are (4w-2)->(5w-2) with odd cofactor 2w-1, valuation a=1, and (8w-12)->(9w-12) with odd cofactor 2w-3, valuation a=2. Here w is respectively 4^(k-i-1)*5^i*v or 8^(k-i-1)*9^i*v. Cofactors are at least five and outputs are even. Taking v a multiple of m fixes the residue of every state at -2 or -12 modulo m.

For fixed k and v->infinity, endpoint ratios converge to (5/4)^k and (9/8)^k. Let alpha=log_2(5/4), beta=log_2(9/8). The ratio alpha/beta is irrational: a rational equality would imply (5/4)^r=(9/8)^s for positive integers r,s, contradicted by prime 5. Thus at least one of alpha/P and beta/P is irrational for any positive P. Choose that corridor, with offset B=2 or 12, denominator A=4 or 8, numerator D=5 or 9, and theta=log_2(D/A). The positive iterates k*theta are dense modulo P by the irrational-rotation theorem.

The two all-length corridor formulas and the exact single-arrow lemmas are kernel checked in the companion source.

## Proof

**Arithmetic progression phase lemma.** Every unbounded positive arithmetic progression with fixed positive step has arbitrarily large elements with phase as close as desired to any prescribed interior phase c in (0,P). For n->infinity, choose the closest progression element to 2^(nP+c). The absolute error is bounded by the fixed step, the relative error tends to zero, and its log-phase tends to c. In particular every phase interval contains arbitrarily large members of every such progression.

Call a cell (r,J) filled if the eventual membership rule for I accepts it. Every cell for an even residue r has arbitrarily large positive even members; infinitude of I implies at least one filled cell. A single element of I above threshold in a cell establishes that the whole cell is filled.

**A. Find a filled cell at the corridor residue r*=-B mod m.** The [all-even-modulus quotient theorem](../agent22-sheep-mixed-hub/MIXED-COMPLETENESS.md) gives a strongly connected graph on even residues, using genuine generic E witnesses. Choose a quotient path from the residue of a filled cell to r*. For any edge r->s along this path, lift one actual witness by Ingredient 1. Its sources form an unbounded progression at r; choose a source above threshold in a filled phase interval. Its target is above threshold by strict increase and belongs to I by closure. Its phase cell at s is filled. Repeat along the finite quotient path. Separate integer witnesses do not need to concatenate: eventual cell membership licenses each new witness.

**B. Fill all phases at r*.** Choose an interior phase c in the filled r* cell. For any target interval J, irrational rotation gives k>=1 with c+k*theta modulo P in the interior of J. Use the progression phase lemma to choose arbitrarily large v multiple of m for which the corridor start A^k*v-B has phase tending to c. The endpoint D^k*v-B then has phase tending to c+k*theta modulo P, by the endpoint ratio limit. For sufficiently large v the start is in the filled cell, and the endpoint lies in J. Closure applies at every genuine corridor edge, so J is filled at r*. Thus all sufficiently large even x with residue r* belong to I.

**C. Spread all-phase fullness.** Suppose every phase cell at r is filled and r->s is any quotient edge. Lift a witness by Ingredient 1. The targets form an unbounded progression at s; choose a sufficiently large target in any desired phase interval. Its source is sufficiently large and in r, hence belongs to I independently of its phase. Closure forces the target into I. Thus every phase cell at s is filled. Strong connectivity propagates this from r* to all residues. QED.

The same proof allows different interval partitions for different residues by finite common refinement and arbitrary finite exceptions below the threshold.

## Evidence and research consequence

- Prior modular-only obstruction: [Agent40, NO-PRESBURGER-INVARIANT](../agent40-sheep-coherent-audit/NO-PRESBURGER-INVARIANT.md). Prior forced a=1 corridor: [Agent40, ROOT-CORRIDOR](../agent40-sheep-coherent-audit/ROOT-CORRIDOR.md). The new contribution combines phase rotation and progression lifts with the existing quotient connectivity, including a second multiplicatively independent corridor. External academic novelty has not been assessed.
- `SheepScaleMixing.lean`: SHA256 `d268a5d75abb90b04cc600f7be573220e42627421b080caacf22ac88fab87808`. Restore Agent16's exact SheepEven.lean (SHA256 `82d1b77cbd8d2071b624834de5796697f6d3b02941ecda08d7f0075cbea846d5`), compile to SheepEven.olean, then compile the new module with LEAN_PATH pointing to that directory. Lean 4.36.0-rc2 commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a compiled the actual section source and all five new declarations. All five axiom profiles were [propext, Quot.sound]; no sorryAx or native_decide. The original TM bridge was not rebuilt here. No CI was dispatched.
- The complete scale-phase theorem additionally depends on the prior paper-level all-modulus connectivity proof and standard real irrational-rotation density. It is not fully Lean formalized.
- This is a method obstruction, not a new excluded blank-reachable exponent. A successful Sheep proof must exploit information beyond finite leading digits, fixed congruences and periodic logarithmic scale. The actual orbit from 10 remains undecided. Do not respond by expanding the accepted 1458 residue family.
