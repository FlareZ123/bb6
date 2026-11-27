# Exact half-depth affine suffix transform

This is intermediate work, not a P1 solution or a Lean-certified numerical result.

Use the definitions and prefix representation in [AffineResidue.lean](AffineResidue.lean). A valid prefix at depth k has parameters (r,a,B), with r < 2^k, B odd, and expr(r,xs)=1+2^k*a. For a full parameter n=r+2^k*T and a d-bit suffix b, define S(q,b)=sum_j b_j*(q+j)*2^j and U(b)=sum_j b_j*2^j, with q=r+k+3.

Expanding expr, including the compulsory initial bit, gives the exact identity
    expr(n,xs++b)=1+2^k*(a+T*B+S(q,b)+2^k*T*U(b)).
Consequently, if d<=k, a valid full word of depth K=k+d exists with this prefix precisely when
    a+T*B+S(q,b) = 0 mod 2^d.
The final term vanishes modulo 2^d. Since B is odd, the supported high parameter residues T are exactly the affine image
    T = -(a+S)*B^{-1} mod 2^d.
All prefixes sharing r use the same suffix support, so this eliminates repeated suffix enumeration. Taking the union over all prefix nodes yields the exact depth-K parameter support, not an approximation.

The canonical prefix half is sufficient at k>=2. Complementing the selected bits other than the compulsory initial bit preserves parameter residue because the two expressions sum to 2+(n+K+1)*2^K. Equivalently, twin nodes satisfy r=r', a+a'=r+k+1 and B+B'=2^k. Opposite appended bits preserve this relation: C+C'=2(r+k+2) and S+S'=2^(k+1), so their parity t agrees and the new a sum is r+k+2+t*2^k. Thus use the seed (2,1,1), retaining one of the two depth-2 nodes. This is a paper argument independent of the previously unsuccessful AffineHalf Lean run.

Suffix support can be built without enumerating all suffix words: start v={0}; for j=d-1,...,0 replace v by the union of 2*v and (2*v+q+j) modulo 2^(d-j). Induction gives precisely the scaled support of the remaining suffix. Stream one row per r, computing odd inverses modulo 2^d and taking the union of affine images.

## Computations performed

The accompanying JS algorithm was executed in the tool runtime. Direct canonical DFS independently agreed at depths 22,24,26. Larger depths use the suffix transform. Counts refer to even residues only; odd n already fails the compulsory first bit.

| K | k | occupied prefix rows | surviving residues | affine image visits |
|---:|---:|---:|---:|---:|
|22|11|120|132208|187392|
|24|12|224|517177|802944|
|26|13|448|1891518|2855720|
|28|14|771|7325739|11710464|
|30|15|1542|26905355|40355616|
|32|16|2809|101625091|166227136|
|34|17|5618|372236349|577108724|

At depth 32, 2,045,858,557 of 2,147,483,648 even residue classes (95.26771293%) are excluded. At depth 34, 8,217,698,243 of 8,589,934,592 even classes (95.66659856%) are excluded. The earlier depth-20 certified count is 36,329 survivors among 524,288. The depth-32 and depth-34 computations are **not** kernel-certified.

For n>=K, the original-source theorem BB6.P1CarryExact.critical_reset_requires_width_full transfers width-zero to impossibility of the critical P1 reset Reach 2 (14*2^n-2*n-10). This concerns that necessary reset, not every P1 gate or the BB(6) upper bound. The paper identity and computations above extend the residue obstruction; the new support count still needs Lean integration and acceptance. No claim that every remaining residue fails.

Reproduce: node affine_suffix.js 22 24 26 28 30 32 34. The script uses exact small integer arithmetic and 32-bit modular multiplication, with bounded k,d. Local shell/Python/Lean tool initialization failed with ClientError in this invocation; JS runtime was available.

## Exact executable

```js
// Exact row-streaming affine suffix support; see AFFINE-SUFFIX.md.
"use strict";
function calc(K,k=Math.ceil(K/2)){
  const d=K-k;
  if(!Number.isInteger(K)||!Number.isInteger(k)||k<2||k>26||d<0||d>k||d>26) throw Error("unsupported depth");
  const M=2**d,mask=M-1,groups=new Map();
  function visit(j,r,a,B){
    if(j===k){
      let g=groups.get(r);if(!g)groups.set(r,g=[]);
      g.push(a,B);return;
    }
    const H=2**j,t=a%2;
    visit(j+1,r+H*t,(a+t*B)/2,B);
    const C=a+r+j+3,S=B+H,u=C%2;
    visit(j+1,r+H*u,(C+u*S)/2,S);
  }
  visit(2,2,1,1);
  function support(q){
    let v=[0];
    for(let j=d-1;j>=0;j--){
      const N=2**(d-j),m=N-1,w=new Uint8Array(N),a=[];
      for(const x of v){
        let z=2*x;
        if(!w[z]){w[z]=1;a.push(z)}
        z=(z+q+j)&m;
        if(!w[z]){w[z]=1;a.push(z)}
      }
      v=a;
    }
    return v;
  }
  function inv(B){
    let x=1;
    for(let i=0;i<5;i++)x=Math.imul(x,2-Math.imul(B,x));
    return x&mask;
  }
  let count=0,visits=0,plan=0,max=0;
  for(const [r,g] of groups){
    const S=support(r+k+3),v=new Uint8Array(M);let n=0;
    plan+=S.length;
    for(let i=0;i<g.length;i+=2){
      const a=g[i],B=g[i+1],I=inv(B);
      if((Math.imul(B,I)&mask)!==(1&mask))throw Error("inverse");
      visits+=S.length;
      for(const s of S){
        const T=Math.imul(-a-s,I)&mask;
        if(!v[T]){v[T]=1;n++}
      }
    }
    count+=n;max=Math.max(max,n);
  }
  return {K,k,d,groups:groups.size,count,visits,plan,max,excluded:1-count/2**(K-1)};
}
if(typeof module!=="undefined")module.exports={calc};
if(typeof require!=="undefined"&&require.main===module)
  for(const K of process.argv.slice(2).map(Number))console.log(JSON.stringify(calc(K)));
```

## Further exact reduction: saturated upper cylinder

Write w_j=(q+j)2^j for j<d. Suppose that for every e=m,...,d-1, there is a weight with valuation exactly e. Pick one such weight per e; these are distinct. The subset sums of the picked weights modulo 2^d are exactly the multiples of 2^m, by triangular binary lifting (at step e the chosen weight toggles bit e without changing lower bits). Thus, separating those picked weights from the other weights, the entire suffix support is the inverse image of its projection modulo 2^m. The odd affine bijection of each prefix preserves that periodicity, as does union across prefixes in the row. Consequently we can construct and count each row at modulus 2^m, then multiply its cardinality by 2^(d-m). No approximation or independence hypothesis is involved.

Choose the smallest m such that all valuations m,...,d-1 occur. The projected suffix support requires only j<m (all later weights vanish). See affine_suffix_period.js. Independently computed results match the prior counts at K=26,32,34, with respective visits 1,633,064; 134,456,608; 328,354,772 instead of 2,855,720; 166,227,136; 577,108,724. At K=34, among 5,618 rows, 3,192 retain all 17 suffix bits, 1,408 collapse two high bits, and 1,018 collapse four high bits. This is a paper-proved optimization and exact-integer test, not an accepted Lean certificate. 

## Formal algebra status

Original-source Lean CI [45965851217](https://github.com/FlareZ123/bb6/actions/runs/45965851217), pinned at a2d799e1ba0ad15d61bac60be6a78e8983a12b5b, passed the standard-axiom audit for expr_suffix, suffix_iff, and width_pos_iff_suffix. These certify the general prefix/suffix equivalence for all k>0 and d<=k, without relying on the canonical-half reduction. The numerical depth-34 count and saturated-cylinder optimization remain paper/executable results, not kernel-certified numeric theorems. Initial CI 45965615677 failed on nonzero witness and rewrite syntax; fixed in the successful commit.
