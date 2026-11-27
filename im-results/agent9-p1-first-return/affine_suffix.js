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
