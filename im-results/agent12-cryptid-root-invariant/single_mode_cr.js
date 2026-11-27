// Exact BigInt/RLE implementation of SingleModeCR.append.lean arithmetic.
// No affine inference and no fuel cutoff inside one section.
function rle(a){let b=[];for(let v of a){v=BigInt(v);if(b.length&&b.at(-1)[0]===v)b.at(-1)[1]++;else b.push([v,1n])}return b}
function cp(a){return a.map(x=>x.slice())}
function push(a,v,n=1n){if(n===0n)return;if(n<0n)throw Error("negative run");if(a[0]?.[0]===v)a[0][1]+=n;else a.unshift([v,n])}
function pop(a){if(!a.length)return 0n;let v=a[0][0];if(a[0][1]===1n)a.shift();else a[0][1]--;return v}
function take(a,v){if(a[0]?.[0]!==v)return 0n;return a.shift()[1]}
function word(r,v,L){let a=cp(L);push(a,v);push(a,0n,r);return a}
function EL(K,r,v,L){let t=0n;
 for(;;){
  if(!K.length)return {K:rle([1]),L:word(r,v,L),t:t+1n};
  let x=pop(K);
  if(v===1n&&!L.length){let q=x/3n;t+=12n*q*q+(6n*r+23n)*q;r+=4n*q;x%=3n}
  if(x===0n){push(K,pop(K)+1n);return {K,L:word(r,v,L),t:t+1n}}
  if(x===1n){let n=1n+take(K,1n);r+=n;t+=2n*n;continue}
  if(x===2n){let n=1n+take(K,2n);L=word(r-1n,v,L);push(L,1n,n-1n);r=1n;v=1n;t+=7n*n;continue}
  push(K,x-3n);push(K,1n,r+2n);push(L,v-1n);
  return {K,L,t:t+8n+4n*r};
 }
}
function DR(K,L){let z=take(L,0n);if(L.length){push(L,pop(L)-1n);push(K,1n,z+2n);return {K,L,t:4n*z+3n}}
 let a=EL(K,z+1n,1n,[]);a.t+=6n*z+8n;return a;
}
function next(s){let K=cp(s.K),L=cp(s.L),k=pop(K),t=0n;
 if(k<1n)throw Error("CR head not positive");
 if(!L.length){let a=k===1n?EL(K,1n,1n,[]):(push(K,k-2n),EL(K,2n,1n,[]));a.t+=k===1n?9n:21n;return a}
 let x=pop(L);
 if(x>=2n)return {halt:true,t:2n};
 if(x===0n){push(K,k+2n);return {K,L,t:2n}}
 if(!L.length){push(K,k);let a=EL(K,3n,1n,[]);a.t+=33n;return a}
 let y=pop(L);
 if(y===0n){push(K,k+3n);push(K,1n);return {K,L,t:5n}}
 if(y===1n){push(K,k);let c=L.length?pop(L)+2n:1n;let a=EL(K,2n,c,L);a.t+=25n;return a}
 push(K,k);push(K,1n);push(L,y-2n);let a=DR(K,L);a.t+=15n;return a
}
const roots={85:{K:rle([3]),L:rle([0,0]),t:11n},490:{K:rle([1]),L:rle([0,0,0,1]),t:28n}};
function mass(s){return s.K.reduce((x,[v,n])=>x+(v+1n)*n,0n)+s.L.reduce((x,[v,n])=>x+(v+2n)*n,0n)}
// Independent literal machine on physical tape: compare normalized head-relative ones.
const tables={85:"1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA",490:"1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"};
function tm(root){return {ones:new Set(),head:0,q:"A",table:tables[root].replaceAll("_","")}}
function literalStep(s){let i=6*(s.q.charCodeAt(0)-65)+3*Number(s.ones.has(s.head)),rule=s.table.slice(i,i+3);if(rule==="---")return false;if(rule[0]==="1")s.ones.add(s.head);else s.ones.delete(s.head);s.head+=rule[1]==="R"?1:-1;s.q=rule[2];return true}
function encoded(s,root=85){let a=tm(root);a.q="C";let flip=root===85?1:-1,p=-1;
 for(let [v,n] of s.K)for(let j=0n;j<n;j++){for(let i=0n;i<v;i++)a.ones.add(flip*p--);p--}
 p=0;for(let [v,n] of s.L)for(let j=0n;j<n;j++){for(let i=0n;i<v+1n;i++)a.ones.add(flip*p++);p++}
 return a
}
function signature(s){return s.q+"|"+[...s.ones].map(i=>i-s.head).sort((a,b)=>a-b).join(",")}
function check(s,a,root){let b=next(s);if(b.t>100000n)throw Error("test cost too high");for(let j=0n;j<b.t;j++)if(!literalStep(a))throw Error("premature halt");
 if(b.halt){if(literalStep(a))throw Error("false halt")}
 else if(signature(a)!==signature(encoded(b,root)))throw Error("endpoint mismatch "+JSON.stringify({s,b,actual:signature(a),want:signature(encoded(b,root))},(_,v)=>typeof v==="bigint"?String(v):v));
 return b
}
function audit(){let states=0,halt=0,moves=0n;let words=[[]];for(let n=1;n<=3;n++)words.push(...words.filter(w=>w.length===n-1).flatMap(w=>[0,1,2,3,4].map(v=>[...w,v])));
 for(let k of [1,2,3,4,7])for(let K of words.filter(w=>w.length<=2))for(let L of words){let s={K:rle([k,...K]),L:rle(L)},b=check(s,encoded(s),85);states++;moves+=b.t;if(b.halt)halt++}
 let rootTests=[];for(let root of [85,490]){let s=roots[root],a=tm(root),t=s.t;for(let j=0n;j<t;j++)if(!literalStep(a))throw Error("root premature halt");if(signature(a)!==signature(encoded(s,root)))throw Error("bad authentic seed "+root);
 let n=0;while(n<100){let p=next(s);if(p.t>100000n||t+p.t>200000n)break;s=check(s,a,root);t+=s.t;n++;if(s.halt)break}rootTests.push({root,n,t:String(t),halt:!!s.halt})}
 return {states,halt,moves:String(moves),rootTests}
}
module.exports={rle,next,roots,mass,audit};
if(require.main===module)console.log(JSON.stringify(audit()));
