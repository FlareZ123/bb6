// Offset-generalized return arithmetic for cryptid #85 and its mirror #490.
// D(c,T)=CR([0],0^5 ++ [c] ++ T), c>0. BigInt, exact raw costs.
// This is a source-derived macro implementation, not a Lean-checked theorem.
function macroModel(){
function token(M,z,tail=[],wantCost=true){
 let x=2n*M+5n,p=z+2n,r=3n,term=true,t=wantCost?4n*M+79n+6n*z:0n;
 for(;;){
  const q=x/3n;
  if(wantCost)t+=12n*q*q+(6n*r+23n)*q;
  r+=4n*q;x%=3n;
  if(x===0n&&term){
   if(wantCost)t+=2n*r+34n;
   x=2n*r+(p>0n?2n:1n);
   if(p>0n)p--;else term=false;
   r=3n;continue;
  }
  if(!term&&tail.length&&x!==0n)return null;
  const h=tail.length?tail[0]+1n:0n,T=tail.slice(1);
  if(x===0n)return {c:2n*r-3n+h,T,t:wantCost?t+2n*r+54n:0n};
  if(x===1n)return {c:2n*(r+p+1n)-3n+h,T,t:wantCost?t+2n*r+4n*p+58n:0n};
  return {c:2n*r-7n,T:[2n*p+5n+h,...T],t:wantCost?t+2n*r+4n*p+64n:0n};
 }
}
function direct(c,T,wantCost=true){
 if(c<=0n)throw Error("expected positive D counter");
 let M=5n,t=0n,tail=[c,...T];
 while(tail.length){
  let x=tail.shift(),q=x/3n;
  if(wantCost)t+=12n*q*q+(6n*M+27n)*q;
  M+=4n*q;x%=3n;
  if(x===0n){M++;continue}
  if(x===2n){let h=tail.length?tail.shift()+1n:0n;return {c:2n*M+9n+h,T:tail,t:wantCost?t+10n*M+136n:0n,rule:"2"}}
  let z=0;while(tail.length&&tail[0]===0n){tail.shift();z++}
  const Z=BigInt(z);
  if(!tail.length)return {c:2n*M-3n,T:[2n*Z+5n],t:wantCost?t+4n*M+91n+4n*Z:0n,rule:"1/end"};
  const v=tail.shift();
  if(v>=3n)return {c:2n*M+1n,T:[...Array(z+2).fill(0n),v-3n,...tail],t:wantCost?t+4n*M+99n+6n*Z:0n,rule:"1/>=3"};
  if(v===1n&&z>0&&!tail.length)return {c:2n*M-3n,T:[2n*Z+1n,5n],t:wantCost?t+4n*M+101n+4n*Z:0n,rule:"1/1"};
  if(v===2n){
   const a=token(M,Z,tail,wantCost);
   return a?{...a,t:t+a.t,rule:"1/2"}:null;
  }
  return null;
 }
 return {c:2n*M+1n,T:[],t:wantCost?t+4n*M+81n:0n,rule:"end"};
}
function fromD(m,c,T){return {q:"CR",L:m.rle([0n]),R:m.rle([0n,0n,0n,0n,0n,c,...T]),K:[]}}
function asD(s){
 if(s.q!=="CR"||s.L.length!==1||s.L[0][0]!==0n||s.L[0][1]!==1n||s.R[0]?.[0]!==0n||s.R[0][1]!==5n||!(s.R[1]?.[0]>0n))return null;
 let c=s.R[1][0],T=[];for(let j=1;j<s.R.length;j++){let [v,n]=s.R[j];if(j===1)n--;if(n>100000n)return null;while(n-->0n)T.push(v)}
 return {c,T};
}
function nextD(m,s,budget=100000,ms=5000){
 const sig=s=>s.q+"|"+["L","R","K"].map(k=>s[k].map(([v,c])=>`${v<3n?v:"+"}:${c===1n?1:"+"}`).join(",")).join("|");
 let t=0n,i=0,j=0,h=new Map(),start=Date.now();
 for(;;){
  if(i){const a=asD(s);if(a)return {...a,t,i,j,s,rule:"fallback"}}
  if(i>=budget||Date.now()-start>ms)return {s,t,i,j,timeout:true};
  let k=sig(s),o=h.get(k);if(o&&i-o.i<=80){let a;try{a=m.affine(o.s,s,i-o.i)}catch{}if(a){if(a.infinite)return {s,t,i,j,infinite:a};s=a.s;t+=a.cost;j++;h.clear();continue}}
  h.set(k,{s,i});let a=m.advance(s);s=a.s;t+=a.cost;i++;if(a.halt)return {s,t,i,j,halt:true};
 }
}
return {direct,token,fromD,asD,nextD}
}
module.exports=macroModel;
if(require.main===module){
 const m=require("./affine_stack_replay.js")(),M=macroModel(),root=process.argv[2]==="85"?85:490,
 seed=root===85?{q:"CR",L:m.rle([0,0]),R:m.rle([2]),K:[]}:{q:"DR",L:m.rle([0,0]),R:m.rle([1]),K:[]};
 let a=M.nextD(m,seed),t=(root===85?11n:7n)+a.t,i=0,fallback=0,counts={};
 const limit=Number(process.argv[3]||10000),cost=process.argv[4]!=="nocost";
 if(a.c===undefined)throw Error("root entry unresolved");
 for(;i<limit;i++){
  let b=M.direct(a.c,a.T,cost);if(!b){fallback++;b=M.nextD(m,M.fromD(m,a.c,a.T));}
  if(b.c===undefined){console.log(JSON.stringify({i,a,b},(_,v)=>typeof v==="bigint"?String(v):v));process.exit(1)}
  counts[b.rule]=(counts[b.rule]||0)+1;if(cost)t+=b.t;a=b;
 }
 console.log(JSON.stringify({root,i,fallback,counts,c:a.c,T:a.T,t:cost?t:null},(_,v)=>typeof v==="bigint"?String(v):v));
}
