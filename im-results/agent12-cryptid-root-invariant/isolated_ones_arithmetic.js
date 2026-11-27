// Arbitrarily many ones separated by nonempty zero runs, plus a final
// zero run. Generalizes the one- and two-one formulas.
function isolated(m,B,A,c,T){
 let t=0n,M=5n,tail=[c,...T];
 for(;;){
   if(!tail.length)return null;
   let x=tail.shift(),q=x/3n;
   t+=12n*q*q+(6n*M+27n)*q;M+=4n*q;x%=3n;
   if(x===0n){M++;continue}
   if(x!==1n)return null;
   break;
 }
 let gaps=[];
 for(;;){
   let z=0;
   while(tail[0]===0n){tail.shift();z++}
   gaps.push(z);
   if(tail[0]!==1n)break;
   tail.shift();
 }
 let k=gaps.length, K=BigInt(k), g=BigInt(gaps[k-1]),
     sum=gaps.reduce((x,y)=>x+BigInt(y),0n);
 const positive=gaps.slice(0,-1).every(x=>x>0);
 const priorPositive=gaps.slice(0,-2).every(x=>x>0);
 if(!tail.length){
   if(!positive)return null;
   const T=gaps.map((x,i)=>2n*BigInt(x)+(i===k-1?5n:1n));
   return {c:2n*M-3n,T,t:t+4n*M+10n*K+81n+4n*sum,rule:"isolated/end"};
 }
 const v=tail.shift(),W=tail;
 if(!priorPositive)return null;
 if(v>=3n){
   if(k===1)return {c:2n*M+1n,T:[...Array(gaps[0]+2).fill(0n),v-3n,...W],t:t+4n*M+99n+6n*g,rule:"isolated/>=3"};
   const T=[...gaps.slice(0,-2).map(x=>2n*BigInt(x)+1n),2n*BigInt(gaps[k-2])+5n,...Array(gaps[k-1]+2).fill(0n),v-3n,...W];
   return {c:2n*M-3n,T,t:t+4n*M+10n*K+89n+4n*sum+2n*g,rule:"isolated/>=3"};
 }
 if(v===2n){
   let x=k===1?2n*M+5n:2n*M+1n;
   let P=k===1?[]:[...gaps.slice(0,-2).map(x=>2n*BigInt(x)+2n),2n*BigInt(gaps[k-2])+6n];
   const h={q:"tEL",L:m.rle([0,0,0,1]),R:m.rle(W),K:m.rle([x,...P,...Array(gaps[k-1]+2).fill(1n),0n])};
   const a=B.nextD(A,h);
   return {...a,t:t+4n*M+10n*K+69n+4n*sum+2n*g+a.t,rule:"isolated/2"};
 }
 return null;
}
module.exports=isolated;
