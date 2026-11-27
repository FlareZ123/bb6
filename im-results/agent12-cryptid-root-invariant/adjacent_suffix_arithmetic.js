// Additional source-derived branches for G(M,1 0^z 1 0^w V).
// Returns exact D0 endpoints or a compact H state, never guesses a result.
function adjacent(m,B,A,c,T) {
 let t=0n,M=5n,tail=[c,...T],x;
 for(;;){
  if(!tail.length)return null;
  x=tail.shift();let q=x/3n;
  t+=12n*q*q+(6n*M+27n)*q;M+=4n*q;x%=3n;
  if(x===0n){M++;continue}
  if(x!==1n)return null;
  break;
 }
 let z=0,w=0;
 while(tail[0]===0n){tail.shift();z++}
 if(tail.shift()!==1n)return null;
 while(tail[0]===0n){tail.shift();w++}
 const Z=BigInt(z),W=BigInt(w);
 if(!tail.length){
  if(z>0)return {c:2n*M-3n,T:[2n*Z+1n,2n*W+5n],t:t+4n*M+101n+4n*Z+4n*W,rule:"11/end"};
  if(w>0)return {c:2n*M-5n,T:[3n,0n,0n,0n,2n*W-1n],t:t+4n*M+137n+4n*W,rule:"11/zero"};
  const h={q:"tEL",L:m.rle([0,0,0,1]),R:[],K:m.rle([2n*M-1n,4n,1n,1n,1n,0n])};
  const a=B.nextD(A,h);return {...a,t:t+4n*M+117n+a.t,rule:"11/token"};
 }
 const v=tail.shift();
 if(v>=3n)return {c:2n*M-3n,T:[2n*Z+5n,...Array(w+2).fill(0n),v-3n,...tail],t:t+4n*M+109n+4n*Z+6n*W,rule:"11/>=3"};
 if(v===2n){
  const h={q:"tEL",L:m.rle([0,0,0,1]),R:m.rle(tail),K:m.rle([2n*M+1n,2n*Z+6n,...Array(w+2).fill(1n),0n])};
  const a=B.nextD(A,h);return {...a,t:t+4n*M+89n+4n*Z+6n*W+a.t,rule:"11/2"};
 }
 if(v===1n&&w===0&&!tail.length&&(z===0||z===1))return {halt:true,t:t+2n*M+(z===0?90n:138n),rule:"11/halt"};
 return null;
}
module.exports=adjacent;
