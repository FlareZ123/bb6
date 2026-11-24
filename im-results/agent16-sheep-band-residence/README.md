# Sheep: uniform subexponential dyadic residence bound

## Theorem (Lean checked, 2026-11-24)

For any finite path x(0),...,x(n) in the original SheepEven.EvenEdge graph, with x(0) even and every x(i) in [2^ell,2^(ell+1)), and any integers k,r >= 1 with ell <= r(k+1),

    n <= (ell+1-k)^r + (2^k+1)*r.

Subtraction is truncated in Nat. This bounds the number of internal even returns, not the physical Turing machine steps. The bound applies to any starting state in the band and includes exceptional source states. It is not a proof of nonhalting.

## Proof

1. A fast edge has x <= 2^k*(y-x). Each internal fast edge contributes at least 2^ell/2^k to a total increment strictly less than 2^ell. Hence there are fewer than 2^k fast edges. In the exact first-even formula, every generic source 2^a*u with a<k is fast, since u is odd and a>=1. Every edge whose odd-run exponent h is positive is also fast: 3*2^h <= 2*3^h implies y-x >= x/2. Exceptional source 3*2^a can occur at most once in a dyadic band. Thus there are at most 2^k separators (fast or exceptional).
2. Each remaining edge has h=0 and k<=a<=ell. It satisfies SheepAffine.Holds (branchParams (a,0)) x y. The exact existing affine word identity for a fixed word w of these letters is L*y+Q=N*x+P with L=2^C, C=sum(a+1), and N odd. If two distinct starts in a band realize the same length-r word, subtracting the identities and canceling the odd coefficient makes their positive difference divisible by 2^C. But C>=ell, and the difference is strictly smaller than 2^ell. Contradiction.
3. Hence at most (ell+1-k)^r indices begin a full length-r slow block. Every other internal-edge index lies at most r-1 positions before a separator or the terminal sentinel n. Each separator/sentinel covers at most r indices. Sum both counts.

Choosing k on the order of sqrt(ell log(ell+1)) and r=ceil(ell/(k+1)) gives 2^{O(sqrt(ell log(ell+1)))} even returns per dyadic band. The polynomial factor from summing over bands is absorbed in the same asymptotic bound. Consequently, any first hit on 2^j from 10 has at most 2^{O(sqrt(j log(j+1)))} even returns. For an infinite orbit this yields superpolynomial growth of the return state as a function of the even-return index. These asymptotic consequences follow on paper from the checked finite theorem. They do not bound the possible halting exponent j.

## Checked code and reproduction

The proof uses the exact original SheepEven model reconstructed by ../agent16-sheep-even-return/reconstruct_all.py, and the existing ../agent16-sheep-aperiodic-words/SheepAffine.lean (SHA256 9304dddff6bc6b179a9f972e9820a6c801118ec2bdc3aa4396667f04a777df7e). Restore those sources into one Lean module directory. Run reconstruct.py in this directory to extract the three new modules; copy them into the same module directory. Set LEAN_PATH=. and compile in this order with Lean 4.36.0-rc2: SheepEven, EvenEdge, SheepAffine, SheepBand, SheepBandSource, SheepBandCounting (lean -o NAME.olean NAME.lean). The three new files were compiled locally. SheepBandCounting.band_path_bound has axioms [propext, Classical.choice, Quot.sound]. No sorryAx. The original raw-machine transport theorem was checked previously (CI 41505950547); this invocation compiled the actual graph modules locally rather than rebuilding the external raw machine.

The separation lemma extends the earlier aperiodic-word result: repeated full words cannot occur at distinct positions in a sufficiently narrow band even without adjacent repetition. This is a structural growth result rather than another terminal-residue exclusion. The proof is filed as intermediate research pending integration into a stronger halting argument.

## Global source-reachability and raw-return bound (kernel checked)

Write B(j,k,r)=(j+1-k)^r+(2^k+1)r+1. For k,r>=1 and j<=r(k+1), every positive even path entirely below 2^j has at most j*B(j,k,r) edges. A path from the genuine first-even state 10 ending at 2^j has at most j*B(j,k,r)+1 edges, counting the final crossing.

Moreover, an exact even edge with hidden odd-run length h satisfies 3^h*x <= 2^h*y because F(x)-1 >= x. Composing along n edges, with H=sum(h), yields both Steps(n+H,x0,xn) and 3^H*x0 <= 2^H*xn. If xn<=2^j and x0>=1, squaring and using 8^H<=9^H gives H<=2j. Thus **the unaccelerated section return count is bounded by j*B(j,k,r)+1+2j**, not j times the even return count.

The actual exported theorem, SheepBandGlobal.reach_power_raw_bound, takes h : SheepEven.EvenReach 10 (2^j) and concludes existence of m within this bound with SheepEven.Steps m 10 (2^j). No bounded-witness assumption is made. This directly composes with the original blank-even reduction; two initial section returns take 5 to 10. Primitive Turing-machine costs remain separate. All theorem axioms are standard; compiled locally under Lean 4.36.0-rc2, no sorryAx.

Reconstruct the fourth module using reconstruct.py, compile the original OddPrefix and EvenReach modules after EvenEdge, then compile SheepBandGlobal after SheepBandCounting and EvenReach. The module SHA256 is 8efc8694c5f8f1f4a14587a5659e1474b544a9af47766ac5ee33a0ec1de6ea10.
