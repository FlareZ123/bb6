// Apache-2.0 source-shaped replay of the pinned Google DeepMind F067 module.
'use strict';
function replay(source) {
 const n=BigInt, check=(b,s)=>{if(!b)throw Error(s)}, eq=(a,b)=>JSON.stringify(a,(_,v)=>typeof v==="bigint"?String(v):v)===JSON.stringify(b,(_,v)=>typeof v==="bigint"?String(v):v);
 const pairs=name=>[...source.match(new RegExp("def "+name+" : RLEStack :=\\s*\\[([\\s\\S]*?)\\]"))[1].matchAll(/\((\d+),\s*(\d+)\)/g)].map(x=>[n(x[1]),n(x[2])]);
 const mid=pairs("midPrefixRLE"),rt=pairs("midRightTailRLE"),ks0=[...source.match(/def ksInitOut : List ℕ :=\s*\[([^\]]+)\]/)[1].matchAll(/\d+/g)].map(x=>n(x[0]));
 const p=(v,c,s)=>!c?s:s.length&&s[0][0]===v?[[v,c+s[0][1]],...s.slice(1)]:[[v,c],...s],one=(v,s)=>p(v,1n,s);
 const pop=s=>{if(!s.length)return null;const [[v,c],...t]=s;return c===0n?pop(t):[v,c===1n?t:[[v,c-1n],...t]]};
 const bump=(o,k,s)=>{if(!k)return s;const a=pop(s);return a?one(a[0]+k,a[1]):o?null:[[k-1n,1n]]};
 const single=(v,s)=>{const a=pop(s);return !!a&&a[0]===v&&!pop(a[1])};
 const peel0=(k,s)=>{for(let i=0;i<k;i++){const a=pop(s);if(!a||a[0]!==0n)return null;s=a[1]}return s};
 const peel3=s=>{let a=pop(s);if(!a||a[0]!==6n)return null;let z=peel0(3,a[1]);if(!z)return null;let b=pop(z);if(!b||b[0]<3n||b[0]%3n)return null;let c=pop(b[1]);if(!c||c[0]!==3n)return null;let d=pop(c[1]);return d&&d[0]===0n?[b[0]/3n-1n,d[1]]:null};
 const peel=s=>{let ks=[];for(let i=0;i<35;i++){let a=peel3(s);if(!a)break;ks.unshift(a[0]);s=a[1]}return [ks,s]};
 const w3=(k,s)=>one(6n,p(0n,3n,one(3n*k+3n,one(3n,one(0n,s))))),w0=(k,s)=>one(6n,p(0n,3n,one(3n*k+3n,p(0n,3n,s)))),body=(z,b)=>one(0n,one(3n,p(0n,z,one(6n,[...mid,[b,1n],[2n,1n]]))));
 const shift=(ks,c=2n)=>ks.map(k=>{let v=k+c;c*=4n;return v});
 const empty=()=>({g:14n,h:0n,d:0n,e:0n,len:0});
 const prepend=(k,a)=>({g:28n*k+390n+4n*a.g+6n*a.d,h:5n*k+136n+a.g+a.h+a.e,d:56n+16n*a.d,e:10n+4n*a.d+4n*a.e,len:a.len+1});
 const agg=ks=>ks.reduceRight((a,k)=>prepend(k,a),empty()),tick=a=>({...a,g:a.g+a.d,h:a.h+a.e});
 const absorb=(k,a)=>[a.len?56n+a.g+14n*k+132n+a.g+a.d:14n*k+216n,prepend(k+1n,tick(tick(a)))];
 const abort=()=>{throw Error("abort")};
 const step=(oL,oR,fast,m,L,R)=>{
 const ret=(m,l,r,c)=>{if(l===null||r===null)abort();return {m,l,r,c}};
 if(m==="F"){
 if(L.length&&L[0][0]===0n&&L[0][1]>=5n){let a=pop(R),b=a&&a[0]===0n&&pop(a[1]);if(b){let k=(L[0][1]-1n)/4n;return ret("F",[[0n,(L[0][1]-1n)%4n+1n],...L.slice(1)],one(0n,one(b[0]+8n*k,b[1])),72n*k)}}
 let a=pop(L);if(!a){if(oL)abort();return ret("AR",[[1n,1n]],R,3n)}
 let [v,L1]=a;
 if(v===0n){let b=pop(L1);if(!b){if(oL)abort();return ret("F",[],one(0n,bump(oR,1n,R)??abort()),3n)}if(b[0]===0n)return ret("F",bump(oL,2n,b[1]),one(0n,R),12n);let R1=bump(oR,1n,R)??abort();return b[0]===1n?ret("F",b[1],one(2n,R1),7n):ret("AR",one(b[0]-2n,b[1]),p(0n,2n,R1),4n)}
 if(v===1n)return {halt:true,c:3n};if(v===2n)return ret("AR",bump(oL,2n,L1),one(0n,bump(oR,1n,R)??abort()),8n);
 let k=v/3n;return ret("F",one(v%3n,L1),one(0n,p(1n,k-1n,bump(oR,1n,R)??abort())),5n*k)
 }
 if(fast&&R.length&&R[0][0]===1n&&R[0][1]>=2n){let a=pop(L),b=a&&a[0]===0n&&pop(a[1]);if(b){let k=R[0][1]-1n;return ret("AR",one(0n,one(b[0]+3n*k,b[1])),[[1n,1n],...R.slice(1)],23n*k)}}
 if(R.length>=2&&R[0][0]===0n&&R[0][1]===1n&&R[1][0]===1n&&R[1][1]>=1n){let a=pop(L),b=a&&a[0]===0n&&pop(a[1]);if(b){let k=R[1][1];return ret("AR",one(0n,one(b[0]+3n*k,b[1])),one(0n,R.slice(2)),9n*k)}}
 let d=pop(R);if(!d){if(oR)abort();return ret("F",L,[[1n,1n]],6n)}
 let [v,R1]=d;
 if(v===0n){let a=pop(L);if(!a){if(oL)abort();return ret("F",[],bump(oR,2n,R1),3n)}if(a[0]===0n)return ret("AR",bump(oL,3n,a[1]),bump(oR,1n,R1),7n);if(a[0]===1n)return ret("F",a[1],bump(oR,4n,R1),7n);let k=a[0]/2n;return ret("AR",one(a[0]%2n,a[1]),one(0n,bump(oR,2n*k,R1)??abort()),4n*k)}
 if(v===1n){let a=pop(R1);if(!a){if(oR)abort();return ret("AR",one(0n,L),[],2n)}return ret("AR",L,one(0n,one(a[0]+1n,a[1])),14n)}
 let k=v/2n;return ret("AR",p(0n,k,L),one(v%2n,R1),2n*k)
 };
 const sub=(fuel,oL,fast,s)=>{let m="F",l=one(0n,s),r=[[9n,1n]],c=0n;for(let i=0;i<fuel;i++){if(m==="AR"&&single(0n,r)){let s=peel0(5,l);if(!s)abort();return {s,c}}let t=step(oL,true,fast,m,l,r);c+=t.c;if(t.halt)return {halt:true,c};({m,l,r}=t)}abort()};
 const steps=(n,oL,oR,fast,m,l,r)=>{let c=0n;for(let i=0;i<n;i++){let t=step(oL,oR,fast,m,l,r);check(!t.halt,"unexpected halt");c+=t.c;({m,l,r}=t)}return {m,l,r,c}};
 let m="F",l=[],r=[[1n,1n]],c1=6n,jumps=0;
 for(let i=0;i<11728;i++){if(m==="F"&&single(5n,r)){let a=pop(l);if(a&&a[0]===0n){let [ks,s]=peel(a[1]);if(ks.length){let t;try{t=sub(100,false,false,s)}catch{}if(t&&!t.halt){jumps++;c1+=t.c+agg(ks).g;l=one(0n,shift(ks).reduce((s,k)=>w3(k,s),t.s));continue}}}}let t=step(false,false,true,m,l,r);check(!t.halt,"phase1 halt");c1+=t.c;({m,l,r}=t)}
 check(m==="F"&&single(5n,r)&&eq(l,one(0n,ks0.reduceRight((s,k)=>w0(k,s),body(56233n,3n)))),"phase1 checkpoint");check(jumps===1062,"jumps");
 let a=empty();for(let k of ks0){let [c,b]=absorb(k,a);c1+=c;a=b}
 const open=s=>{let costs=[];for(let i=0;i<10;i++){let t=sub(50,true,true,s);check(!t.halt,"open halt");costs.push(t.c);s=t.s}return {costs,s}};
 const z=open([[0n,1n],[3n,1n],[0n,9n],[6n,1n]]),q=open([[0n,1n],[3n,1n],[0n,10n]]);
 check(eq(z.s,[[0n,1n],[3n,2n],[0n,2n],[12n,1n],[3n,1n],[0n,1n],[3n,1n],[9n,1n]]),"open zero");
 check(eq(q.s,[[0n,1n],[3n,2n],[0n,2n],[12n,1n],[3n,1n],[0n,1n],[3n,2n]]),"open pos");
 const B=steps(189,true,true,true,"F",one(0n,mid),[[0n,1n],[1n,2n]]),D=steps(83,true,true,true,"AR",[],one(28n,rt));
 check(B.m==="AR"&&eq(B.l,[[0n,1n]])&&eq(B.r,[[0n,1n],[3n,1n],[0n,1n],[18n,1n],...rt]),"B checkpoint");
 check(D.m==="AR"&&eq(D.l,[[0n,1n],[3n,1n],...mid])&&eq(D.r,[[1n,1n]]),"D checkpoint");
 let c2=0n;
 for(let k=0n;k<7029n;k++){let m=7028n-k;for(let c of (m===0n?z:q).costs){c2+=c+a.g;a=tick(a)}c2+=160n*m+28n*k+397n+B.c+D.c+a.g;a=tick(a);let [c,b]=absorb(4n,a);c2+=c;a=b}
 let c3=0n,s=body(1n,21090n),halt=false,i=0;
 for(;i<186;i++){let [ks,u]=peel(s);for(let j=ks.length-1;j>=0;j--)a=prepend(ks[j],a);let t=sub(400,false,true,u);if(t.halt){c3+=a.h+t.c;halt=true;break}c3+=a.g+t.c;a=tick(a);s=t.s}
 check(halt&&i===185,"phase3 halt");
 const total=c1+c2+c3;
 return {summary:{jumps,phase1:String(c1),partB:String(B.c),partD:String(D.c),openZero:z.costs.map(String),openPositive:q.costs.map(String),finalTowerDepth:a.len,phase3count:i+1,totalBits:total.toString(2).length,totalDigits:String(total).length,totalPrefix:String(total).slice(0,70),totalSuffix:String(total).slice(-70)},total:String(total)};
}
module.exports=replay;
if(require.main===module){console.log(JSON.stringify(replay(require('node:fs').readFileSync(process.argv[2],'utf8')),null,2));}
