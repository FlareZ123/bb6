// Regression of the correction-delay identity and isolated odd-gap relay.
// node delayed_correction_regression.js
function pre(n) {
  let q=n,C=0n,L=0,E=0;
  while(q>0n) {
    let j=0; while((q&1n)===0n){q>>=1n;j++}
    q>>=1n;
    const e=Math.floor((5*j+1)/2);
    C=(4n*C+(1n<<BigInt(j+2))-1n)<<BigInt(e);
    E+=e+2;L+=j+1;
    if(!(j%2))return {q,C,L,E,p:(L-1)/2,lastR:j/2};
  }
  return null;
}
let N=268311341n,W=29,S=0,H=[],head=0,ps=[];
let count=0,clean=0,oddTotal=0,map={};
for(let t=0;t<20000;t++){
  let z=pre(N);if(!z)throw Error("unexpected gate");
  oddTotal+=z.p%2;
  let u=z.C>>BigInt(5*z.lastR);
  if(!(u&1n)||z.C!==(u<<BigInt(5*z.lastR)))throw Error("valuation");
  while(head<H.length&&H[head]<S+z.L)head++;
  N=(1n<<BigInt(W+z.E))+z.q-z.C;
  let k=5*z.lastR,mask=(1n<<BigInt(k))-1n;
  if((N&mask)!==(z.q&mask))throw Error("delay");
  let next=pre(N);if(next&&next.L<=k)clean++;
  S+=z.L;W+=z.E+1;H.push(S+W-1);ps.push(z.p);
  if(head>0&&H[head-1]===S-1&&head<H.length-1){
    let g=H[head]-H[head-1],q=ps[head];
    if(g===7*q+4&&q%4===1&&g<=k&&(z.q&((1n<<BigInt(g))-1n))===(1n<<BigInt(g-1))){
      if(!next||next.p!==(g-1)/2||next.p%2!==1)throw Error("relay");
      count++;map[q]=(map[q]||0)+1;
    }
  }
}
console.log(JSON.stringify({returns:ps.length,cleanFollowingPrefix:clean,oddGapRelays:count,oddTotal,map}));
