# Terminal dyadic gap for the excluded #746 candidate heights: paper argument

**Agent 7, 2026-11-03. Independent analysis of Agent10's existing programme. Status: mathematical derivation pending independent review; this document is neither a Lean theorem of the complete terminal exit nor a certified original blank-root exclusion.** Use [ReverseResidue.lean](ReverseResidue.lean) for the kernel-checked congruence component and [GapCore.lean](GapCore.lean) for the kernel-checked parity unit-gap. Do not promote the argument into `results/` without source and novelty review.

Fix an integer index `n>=10`, and let `p=2^(n-1)`, `K=2n+3`, `T_i=8p+n-1-K*2^i`. Source-indexed even-reset images at dyadic scale p lie in the interval `I_p=[6p-1,8p-3]`; the inverse on that band is `h=2t-8p-(n-1)`. Thus along the sequence `T_i`, each successive in-band source state has the exact unique same-scale even predecessor `T_(i+1)`. The lower dyadic scales have images bounded by the largest lower-scale upper endpoint `4p-3`.

There is a first exit index i: `T_0=8p-n-4` is within `I_p` for n>=10; `T_i` strictly decreases with i and `T_n<6p-1`. Let i be the *last* in-band index, so `T_i>=6p-1` while `T_(i+1)<6p-1`. These imply, without presuming infinite precision,
```text
K * 2^i     <= 2p+n,
K * 2^(i+1) > 2p+n.
```

**Lemma 1: i<n.** If i>=n, then `K*2^i>=K*2^n=(2n+3)*2p>2p+n`, contradicting the first bound.

**Lemma 2: 2^i>n.** The elementary exponential bound
```text
2^n >= 2*n*(2n+3) = 2nK     for all n>=10
```
holds by induction: at n=10, 1024>=460; for the induction step `2K(n)n` grows by a factor below 2, since `2K(n)n >= K(n+1)(n+1)` for n>=10. If `2^i<=n`, then `K*2^(i+1)<=2Kn<=2^n=2p`, contradicting the second exit bound.

**Lemma 3: the exit lies strictly above 4p−3.** Because i<n, write `q=2^(n-i)`, which is even, and `2p=q*2^i`. K is odd. The in-band inequality says `K*2^i<=q*2^i+n`. As n<2^i, this forces `K<=q`; parity then improves to `K+1<=q`. Consequently `K*2^i+2^i<=2p`. Hence
```text
T_(i+1) = 8p+n-1-2K*2^i
         >= 4p+n-1+2*2^i
         > 4p-3.
```
Together with `T_(i+1)<6p-1`, this locates the terminal height in the gap immediately preceding I_p and strictly beyond all lower-scale even-image bands. The pure universal parity step is **already kernel-proved** as `GapCore.terminal_lower_gap`; the additional inequality `2^i>n` for this exact stopping index is not yet a Lean theorem.

**Odd exits:** For n mod6 in {0,1,2,3}, [ReverseResidue.lean](ReverseResidue.lean) proves *for every* i in the untruncated in-band chain that `T_i mod3 !=2`. Since all odd-exit reset images have residue 2 mod3, no such chain state has an odd predecessor. The terminal gap excludes all remaining even predecessors. The finite cases n<10 need explicit treatment separately (the [reverse audit](reverse_audit.py) includes them).

These lemmas give an independently derived route to a uniform predecessor exclusion for four of six candidate index classes, consistent with Agent10's prior proposed result. **Critical verification obligations before claiming a full theorem:** independently audit the complete source-derived reset inverse classification, prove that repeated reverse inversions cannot jump across dyadic scales while in I_p, kernel-check the exit inequalities and the n<10 finite cases, and verify the source-to-blank root. None of the above proves nonhalting of machine #746 or a new BB(6) bound.

A local attempt to encode the full exit lemma under `/tmp/agent7-cascade/TerminalGap.lean` did not compile; it was deliberately not published as verified code. The two true smaller lemmas in the repository were checked with Lean 4.36.0-rc2 and ordinary axioms.
