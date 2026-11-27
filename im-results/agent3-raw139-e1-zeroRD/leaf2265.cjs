/* Exact arithmetic candidate for D0=1LF residual 2265. See Leaf2265.md
   for the primitive-frame proof. Node.js, no external dependencies.
   The all-parameter identities are paper proved, not Lean accepted. */
"use strict";
const TABLE=[7,20,11,1,14,11,22,16,24,13,2,12];
function normalize(k,w){while(w.startsWith("01")){k++;w=w.slice(2)}return [k,w.replace(/0+$/,"")]}
function next(k,w){
 if(k<1n||w.startsWith("01"))throw Error("bad section");
 if(w.startsWith("1"))return [...normalize(k+1n,"0"+w.slice(1)),4n*k+2n];
 let z=w+"000",m=0;while(z[2+m]==="1")m++;
 let U=z.slice(3+m).replace(/0+$/,""),r=Math.floor(m/4),j=m%4,Z="1100",a,t,c;
 if(j===3)return ["hole",2n*k+13n+10n*BigInt(r)];
 if(j===1)return [...normalize(k+(r===0?4n:3n),r===0?U:"000"+Z.repeat(r-1)+"111"+U),8n*k+20n+10n*BigInt(r)];
 t=(k-(j===0?1n:0n))/2n;a=2n+5n*t;c=4n*k+19n+10n*BigInt(r)+30n*t*t+32n*t;
 if(j===0){
  if(k%2n)return [...normalize(a,r===0?"000101"+U:"0001000"+Z.repeat(r-1)+"111"+U),c];
  return [...normalize(a+(r===0?6n:5n),r===0?U:"000"+Z.repeat(r-1)+"111"+U),c+8n*a+20n]
 }
 if(k%2n===0n)return [...normalize(a,"000"+Z.repeat(r)+"111"+U),c];
 return [...normalize(a+(r===0?7n:6n),r===0?U:"000"+Z.repeat(r-1)+"111"+U),c+12n*a+42n]
}
function primitive(k,w,n){
 const word="01".repeat(k)+w;let l=0n,r=BigInt("0b"+(word.split("").reverse().join("")||"0")),q=0;
 for(let t=0;t<=n;t++){
  const v=TABLE[2*q+Number(r&1n)];
  if(v===24)return ["hole",BigInt(t)];
  if(t===n){if(l!==0n||q!==0)throw Error("not a boundary");let a=0n;while((r&3n)===2n){a++;r>>=2n}
   return [a,r===0n?"":r.toString(2).split("").reverse().join(""),BigInt(n)]}
  let b=BigInt(v>>1&1);if(v&1){l=l<<1n|b;r>>=1n}else{r=(r>>1n)<<2n|b<<1n|l&1n;l>>=1n}q=v>>2
 }
}
const j=x=>JSON.stringify(x,(_,v)=>typeof v==="bigint"?v.toString():v);
if(j(primitive(0,"",13))!==j([3n,"",13n]))throw Error("blank seed");
let checks=0;
for(let k=1;k<=15;k++)for(let m=0;m<=24;m++)for(let u of ["","1","101101","001110101"]){
 let w=("00"+"1".repeat(m)+"0"+u).replace(/0+$/,""),a=next(BigInt(k),w),b=primitive(k,w,Number(a.at(-1)));
 if(j(a)!==j(b))throw Error(j({k,w,a,b}));checks++
}
let k=3n,w="",T=13n,trace=[];
for(let i=0;i<10000;i++){
 trace.push({i,k,w,T});let a=next(k,w);
 if(a[0]==="hole"){
  const N=T+a[1];const expected=808309055302710301732399105636921133919495108874980019743107699471600464749233442847378894817095810992429166948707568686931771651390236209884096433253525595914426390935828906878170789519869183115472163083845213146412559801558627n;
  if(i!==435||w!=="001110111"||N!==expected)throw Error("unexpected terminal");
  const result={checks,sections:i,endpoint:{k,w,T,queryCost:a[1]},firstE0:N,weightedBound:N+6n,trace};
  if(typeof module!=="undefined")console.log(j(result));else text(j(result));
  break
 }
 [k,w]=a;T+=a[2];
}
