"use strict";
const cap=Number(process.argv[2]||3310000);
const run1=x=>{const t=x+1n;return (t&-t).toString(2).length-1};
const ones=k=>(1n<<BigInt(k))-1n;
const near=(x,n=100)=>x.toString(2).split("").reverse().join("").slice(0,n);
let l=6n,r=0n,live=3n,returns=0,bEntries=0n,events=[],halt=null,bad=null;
function primitive(tmax){
 const table="1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF".replaceAll("_","").match(/.../g);
 let L=0n,R=0n,q=0,t=0;
 for(;t<tmax;t++){const a=table[2*q+Number(R&1n)];if(a==="---")break;const w=BigInt(a[0]);q=a.charCodeAt(2)-65;
  if(a[1]==="R"){L=(L<<1n)|w;R>>=1n}else{R=(R>>1n<<2n)|(w<<1n)|(L&1n);L>>=1n}}
 return {t,q,L:(L<<1n)|(R&1n),R:R>>2n,pending:(R>>1n)&1n};
}
for(;returns<cap;returns++){
 for(;;){const x=Number(r&15n);
  if((x&7)===7){const k=Math.floor(run1(r)/3),m=3n*BigInt(k);l=(l<<m)|2n*((1n<<m)-1n)/7n;r>>=m;live+=5n*BigInt(k);continue}
  if(!(x&1)){if(x&2){l=(l<<2n)|2n;r>>=2n;live+=4n;continue}l>>=1n;r=((r>>2n)<<2n)|2n;live+=6n;break}
  if(x&2){l=(l<<3n)|10n;r>>=3n;live+=13n;continue}
  if(x&4){if(x&8){l=(l<<4n)|10n;r>>=4n;live+=10n;continue}l=(l<<1n)|1n;r=((r>>4n)<<2n)|2n;live+=12n;break}
  if(x&8){halt={returns,live:live.toString(),haltingQuery:(live+4n).toString(),l:near(l),r:near(r)};break}
  l=(l<<4n)|6n;r>>=4n;live+=4n;
 }
 if(halt)break;
 for(;;){const a=run1(l);bEntries++;
  if(a>=3){const ev={returns,a,live:live.toString(),l:near(l),rTail:near(r),leftBits:l.toString(2).length,rightBits:r.toString(2).length};events.push(ev);
   if(events.length===1&&process.argv[3]==="primitive-check"){const p=primitive(Number(live));if(p.t!==Number(live)||p.q!==1||p.pending!==0n||p.L!==l||p.R!==r)throw Error("primitive mismatch");ev.primitiveExactMatch=true}
   if(a!==3||(l&63n)!==39n){bad=ev;break}}
  if(a%2===0){l=(l>>BigInt(a+1)<<2n)|2n;r<<=BigInt(a);live+=BigInt(a+2);break}
  l>>=BigInt(a+1);r<<=BigInt(a+1);const k=run1(l);l>>=BigInt(k+1);r=(r<<BigInt(k+1))|ones(k+1);
  if(l&1n){l=(l>>1n<<2n)|2n;live+=BigInt(a+k+6);break}
  l>>=1n;r<<=1n;live+=BigInt(a+k+5);
 }
 if(bad)break;
}
console.log(JSON.stringify({returns,live:live.toString(),bEntries:bEntries.toString(),events,bad,halt},null,2));
