// All binary triple-containing words: exact source-rule cost algorithm.
// Reproduce with node general_triple_barrier.js. No inferred affine jumps.
const m=require("./affine_stack_replay.js")();
const good=X=>X.length>0&&X[0]>0&&X[0]!==2&&X.every((a,i)=>a!==2||(i>1&&X[i-1]===1));
function arithmetic(X,L){
 X=X.slice();L=L.slice();let t=0,high=0,low0=0,low2=0,maxd=0;
 while(true){
  if(!good(X)||!L.join("").includes("111"))throw Error("invariant "+JSON.stringify({X,L}));
  if(L[0]===0){L.shift();X[0]+=2;t+=2;continue}
  if(L[1]===0){L.splice(0,2);X[0]+=3;X.unshift(1);t+=5;continue}
  let d=0;while(X[d]===1)d++;
  if(X[d]>=3){
   let a=X[d]-3,c=L[2];t+=41+6*d;high++;maxd=Math.max(d,maxd);
   if(c===1)return {t:t+2,high,low0,low2,maxd};
   L.splice(0,3,1);X=[...Array(d+4).fill(1),a,...X.slice(d+1)];continue
  }
  let b=0,b1=0,b2=0,z=0;
  while(X[b]===1||X[b]===2){if(X[b]===1){b1++;z++}else{b2++;z=0}b++}
  if(X[b]>=3){
   if(!b2)throw Error("unexpected high");
   low2++;return {t:t+40+4*b1+10*b2+2*z,high,low0,low2,maxd}
  }
  low0++;return {t:t+32+4*b1+10*b2,high,low0,low2,maxd};
 }
}
function run(s){
 let t=0n;
 for(let i=0;i<10000;i++){let a=m.advance(s);s=a.s;t+=a.cost;if(a.halt)return Number(t)}
 throw Error("timeout");
}
function check(got,a,context){if(got!==a.t)throw Error(JSON.stringify({...context,a,got}))}
if(require.main===module){
 let stats={tested:0,high:0,low0:0,low2:0,maxd:0,maxT:0};
 for(let n=3;n<=15;n++)for(let i=0;i<2**n;i++){
  let U=i.toString(2).padStart(n,"0");if(!U.includes("111"))continue;
  let L=U.split("").reverse().map(Number),a=arithmetic([3],L);
  let got=run({q:"tCR",L:m.rle([...L,0,0,1]),K:m.rle([3,0,0]),R:[]});
  check(got,a,{U});stats.tested++;
  for(let k of ["high","low0","low2"])stats[k]+=a[k];
  stats.maxd=Math.max(stats.maxd,a.maxd);stats.maxT=Math.max(stats.maxT,a.t);
 }
 let extra={tested:0,high:0,low0:0,low2:0};
 for(let X of [[1,1,2],[1,1,2,1,2,3],[1,1,2,1,2,0,7],[1,1,2,1,1,3],[1,1,1],[3,1,2],[7,1,2,0],[1,0,2],[1,1,2,1,1,2,8],[1,1,2,2],[1,3,1,2]]){
  if(!good(X))continue;
  for(let L of [[1,1,1],[1,1,0,1,1,1],[0,1,0,1,1,1],[1,1,0,1,1,0,1,1,1]]){
   let a=arithmetic(X,L),got=run({q:"tCR",L:m.rle([...L,9,0,1]),K:m.rle([...X,0,0]),R:m.rle([5,4])});
   check(got,a,{X,L});extra.tested++;
   for(let k of ["high","low0","low2"])extra[k]+=a[k];
  }
 }
 console.log(JSON.stringify({stats,extra}));
}
module.exports={good,arithmetic};
