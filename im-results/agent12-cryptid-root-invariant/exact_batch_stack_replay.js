// Direct quotient acceleration of two exact source-clause cycles.
// Distinct from the experimental affine detector: no inferred period or
// guard extrapolation is used. The paired-stack transcription remains
// a computational model; see TokenCounterCorrection.append.lean for H.
function exactBatch(m) {
  function prepend(a,v,n=1n) {
    if(n===0n)return;
    if(a.length && a[0][0]===v)a[0][1]+=n;
    else a.unshift([v,n]);
  }
  function remove(a) {
    if(a[0][1]===1n)a.shift(); else a[0][1]--;
  }
  function jump(s) {
    const {L,R,K,q}=s;
    // H(x,r,K,W) -> H(x mod 3,r+4 floor(x/3),K,W)
    if(q==="tEL" && L.length===2 && L[0][0]===0n && L[0][1]>0n &&
       L[1][0]===1n && L[1][1]===1n && K.length && K[0][0]>=3n) {
      const a=K[0][0]/3n,r=L[0][1],b=K[0][0]%3n;
      const next=m.clone(s);remove(next.K);prepend(next.K,b);
      next.L[0][1]+=4n*a;
      return {s:next,cost:12n*a*a+(6n*r+23n)*a,rule:"token",cycles:a};
    }
    // G(M,[x]++T) -> G(M+4 floor(x/3),[x mod 3]++T).
    if(q==="CR" && L.length===1 && L[0][0]===0n && L[0][1]===1n &&
       R.length>=2 && R[0][0]===0n && R[0][1]>=1n && R[1][0]>=3n) {
      const a=R[1][0]/3n,M=R[0][1],b=R[1][0]%3n;
      const next=m.clone(s),tail=next.R.slice(1);remove(tail);
      prepend(tail,b);prepend(tail,0n,M+4n*a);next.R=tail;
      return {s:next,cost:12n*a*a+(6n*M+27n)*a,rule:"ordinary",cycles:a};
    }
    return null;
  }
  function nextD(M,s,budget=100000,ms=10000) {
    let t=0n,i=0,j=0,counts={ordinary:0,token:0},start=Date.now();
    for(;;) {
      if(i){const a=M.asD(s);if(a)return {...a,t,i,j,s,counts,rule:"batch"}}
      if(i>=budget||Date.now()-start>ms)return {s,t,i,j,counts,timeout:true};
      const a=jump(s)||m.advance(s);
      if(a.cycles){j++;counts[a.rule]++}
      t+=a.cost;s=a.s;i++;
      if(a.halt)return {s,t,i,j,counts,halt:true};
    }
  }
  return {jump,nextD};
}
module.exports=exactBatch;
