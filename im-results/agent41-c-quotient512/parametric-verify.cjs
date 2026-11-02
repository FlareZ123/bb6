'use strict';
/** @file Independent Machine C finite-quotient BFS using JavaScript exact integers. */
const { performance } = require('node:perf_hooks');
const m = Number(process.argv[2]), base = Number(process.argv[3] || 8);
if (!Number.isSafeInteger(m) || m < 8 || m % 2 ||
    !Number.isSafeInteger(base) || base < 8 || base > m)
  throw Error('invalid parameters');
const n = m + base, total = n ** 3;
if (total >= 2147483648) throw Error('index bound');
const q = x => x < base ? x : base + (x-base) % m;
const encode = (a,k,c) => a*n*n + k*n + c;
/** @param {number} a @param {number} k @param {number} c
 * @returns {[number,number,number] | null} */
function next(a,k,c) {
  if (c===1) return [a,k+1,0];
  if (c===2) return null;
  if (c===3) return [a,k+2,1];
  if (c===0) {
    if (a===0) return [1,0,2*k+2];
    if (a===1) return k===0 ? [5,0,1] : [2,2,2*k-1];
    return [a-2,1,2*k+1];
  }
  if (a===0) return k%2===0 ? [2*k+2,2,c-3] : [2*k+3,0,c];
  return [a-1,k+1,c-1];
}
const seen = new Uint8Array(total), queue = new Int32Array(total);
let head=0,tail=1,edges=0;
queue[0]=encode(5,0,1);seen[queue[0]]=1;
const started=performance.now();
while(head<tail) {
  const v=queue[head++], a=Math.floor(v/(n*n)), k=Math.floor(v/n)%n, c=v%n;
  const aa=a<base?[a]:[a,a+m], kk=k<base?[k]:[k,k+m], cc=c<base?[c]:[c,c+m];
  for(const x of aa)for(const y of kk)for(const z of cc){
    const t=next(x,y,z);
    if(t===null)continue;
    ++edges;
    const id=encode(q(t[0]),q(t[1]),q(t[2]));
    if(!seen[id]){seen[id]=1;queue[tail++]=id;}
  }
}
const reset=[],side=[];
for(let j=0;j<m;++j){
  if(!seen[encode(q(2*(j+m)+1),q(3*(j+m)+4),0)])reset.push(j);
  if(!seen[encode(0,q(4*(j+m)),q(24*(j+m)+23))])side.push(j);
}
console.log(JSON.stringify({base,m,total,reached:tail,edges,reset,side,
  elapsedSeconds:(performance.now()-started)/1000}));
