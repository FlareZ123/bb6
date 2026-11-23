#!/usr/bin/env node
// Quantified #746 t=3 source-parentless 162-index packet regression.
// Usage: node third_fork_packet_leaves.mjs <n> [max-packets]
const [arg, capArg] = process.argv.slice(2);
if (!/^\d+$/.test(arg||'')) throw Error('usage: node third_fork_packet_leaves.mjs <n> [max-packets]');
const n=Number(arg);
if (!Number.isSafeInteger(n) || n<257 || (n%6!==4 && n%6!==5)) {
  throw Error('require n >= 257 and n modulo 6 in {4,5}');
}
const N=BigInt(n),p=1n<<N,c=2n*N+3n,a=c.toString(2).length-1,J=n-a;
const B=Math.floor((J-13)/162);
let cap=B;
if(capArg!==undefined) {
  cap=Number(capArg);
  if (!Number.isSafeInteger(cap) || cap<0 || cap>B) throw Error('invalid max-packets');
}
const A=8n*p+2n*N+3n, k=BigInt(n-3), pk=1n<<k;
let total=0, first=[];
const distinct=new Set();
for(let b=0;b<cap;b++) {
  let count=0,dead=0,cases=[];
  for(let j=162*b;j<162*(b+1);j+=2) {
    const X=A-2n*c*(1n<<BigInt(j));
    if(X%81n!==0n)continue;
    count++;
    const d=X/81n, h=16n*d-p-N-2n, sourceQ=8n*d;
    if(d<=0n || d%2n!==1n || h<0n ||
      sourceQ<6n*pk+1n || sourceQ>8n*pk-1n ||
      2n*(sourceQ)!==8n*pk+h+k+5n || 81n*d!==X)
      throw Error('source odd t=3 band/equation failure n='+n+' j='+j);
    if(2n*h<=p || 4n*h+4n>=3n*p)
      throw Error('even gap failure n='+n+' j='+j);
    const parentless=(h%3n!==2n);
    if(parentless) {
      dead++;
      const key=h.toString();
      if(distinct.has(key))throw Error('duplicate t3 parent across depths');
      distinct.add(key);
    }
    cases.push({j,Xmod243:Number(X%243n),dmod3:Number(d%3n),hmod3:Number(h%3n),parentless});
  }
  if(count!==3 || dead!==2 ||
    cases.map(x=>x.dmod3).sort().join(',')!=='0,1,2')
    throw Error('three-residue packet prediction failed b='+b);
  total+=dead;
  if(b<2)first.push({packet:b,cases});
}
console.log(JSON.stringify({n,J,completePackets:B,checkedPackets:cap,
  genuineThirdValuationParents:3*cap,distinctSourceParentless:total,
  predictedLowerBound:2*cap,allChecked:true,first},null,2));
