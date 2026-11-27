// Exact 3-cell block simulation; no F1 transition is provided.
// Node: node Raw140DoubleGrowth.js
const tails=["64","62","6421","6221","62542","6405"];
const offsets=[[-2,-1,-1],[-2,-2,-1],[-1,-1,-1],[-2,-1,-1],[-1,-1,0],[-1,-1,-1]];
const next=[["6405","62","6221"],["6421","62542","64"],["62","6221","6405"],["62542","64","6421"],["6221","6405","62"],["64","6421","62542"]];
function exits(f){
 const t=[7,23,11,12,15,1,6,18,4,17,f,24],e={};
 for(let q=0;q<6;q++)for(let d=0;d<2;d++)for(let a=0;a<8;a++){
  let p=d?0:2,b=a,r=q,k=0;
  while(p>=0&&p<3&&k<145){let c=t[2*r+((b>>p)&1)];if(c===24)break;
   b=(b&~(1<<p))|(((c>>1)&1)<<p);r=c>>2;p+=(c&1)?1:-1;k++}
  if(p<0||p>=3)e[[q,d,a]]=[r,p>=3?1:0,b,k];
 }return e;
}
function run(f,m,n,s,limit=300000000){
 let e=exits(f),L=[],R=[],q=2,d=1,t=2,j=0;
 if(m===null)L=[6];else{L=Array(m).fill(5);R=("644".repeat(n)+s).split("").map(Number).reverse();q=1;d=1;t=0}
 while(t<limit){
  let S=d?R:L,a=S.length?S[S.length-1]:0;
  if(q===1&&d===1&&a===6&&(m===null||j>0)){
   let l=L.slice().reverse().join(""),r=R.slice().reverse().join(""),match=r.match(/^(644)+/);
   if(/^5+$/.test(l)&&match&&tails.includes(r.slice(match[0].length)))
    return {m:l.length,n:match[0].length/3,s:r.slice(match[0].length),t,j};
  }
  let z=e[[q,d,a]];if(!z)throw Error("non-exiting block "+[q,d,a,t]);
  S.pop();[q,d,a]=z;t+=z[3];j++;let D=d?L:R;if(D.length||a)D.push(a);
 }throw Error("limit "+t);
}
function predict(f,m,n,s){let p=m+(f===13?2:0),r=(p%6)/2,i=tails.indexOf(s);
 return {m:2*m+(f===13?16:14),n:n+Math.floor(p/6)+offsets[i][r],s:next[i][r]}}
function check(f,m,n,s){let a=run(f,m,n,s),b=predict(f,m,n,s);for(let k of ["m","n","s"])if(a[k]!==b[k])throw Error(JSON.stringify({f,m,n,s,a,b}));return a}
for(let f of [4,13]){let a=run(f,null);console.log("root",f,a);for(let i=0;i<5;i++){a=check(f,a.m,a.n,a.s);console.log("return",f,a)}for(let m=18;m<=36;m+=2)for(let s of tails)check(f,m,2,s);console.log("60 parameter samples passed",f)}
