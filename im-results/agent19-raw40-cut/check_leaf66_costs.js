// Exact primitive-cost and absolute-head diagnostic; no proof search.
const rows="1RB0LA_1RC0RE_0RD1LC_1LD1LA_---0RF_1RA1RF".replaceAll("_","").match(/.../g);
const rep=(b,n)=>Array(n).fill(b);
const enc=v=>v.flatMap(([g,c])=>[...rep(0,g),...rep(1,c)]);
const A=(k,b,U,V)=>({q:0,l:[0,...rep(1,k),...enc(U.map(x=>[1,x]))],r:[...rep(1,b),...enc(V)]});
function canon(z){let l=z.l.slice(),r=z.r.slice();while(l.length>1&&l.at(-1)===0)l.pop();while(r.length&&r.at(-1)===0)r.pop();return {q:z.q,l,r}}
function run(z,N){let q=z.q,h=0,t=new Set();z.l.forEach((b,i)=>{if(b)t.add(-i)});z.r.forEach((b,i)=>{if(b)t.add(i+1)});for(let i=0;i<N;i++){const m=rows[2*q+Number(t.has(h))];if(m==="---")throw Error("hole "+i);if(m[0]==="1")t.add(h);else t.delete(h);h+=m[1]==="R"?1:-1;q=m.charCodeAt(2)-65}let lo=h,hi=h;for(let x of t){lo=Math.min(lo,x);hi=Math.max(hi,x)}let l=[],r=[];for(let x=h;x>=lo;x--)l.push(Number(t.has(x)));for(let x=h+1;x<=hi;x++)r.push(Number(t.has(x)));return {q,l,r,h}}
const eq=(a,b)=>JSON.stringify(canon(a))===JSON.stringify(canon(b));
const check=(a,b,cost,shift,label)=>{const z=run(a,cost);if(!eq(z,b)||z.h!==shift)throw Error(JSON.stringify({label,a,b,cost,shift,z}));};
const T=(j,x)=>(2*j+3)*x+80*2**j-14*j-63;
const G=n=>80*2**n-22*n-80;
const C=n=>160*2**n-14*n-66;
const inc=U=>U.length?[U[0]+1,...U.slice(1)]:[1];
let drains=0,gaps=0,roots=[];
for(let j=1;j<=7;j++)for(let x=1;x<=5;x++)for(let U of [[],[1],[3,2]])for(let S of [[],[[3,7]],[[9,4],[3,2]]]){
 const a=A(j===1?x:1,6,j===1?U:[...rep(1,j-2),x,...U],[[5*j+3,3],...S]);
 const b=A(0,j===1?x+14:x+5*j+9,[...rep(1,j),...inc(U)],S);
 check(a,b,T(j,x),3-x,"standard drain");drains++;
}
for(let n=1;n<=7;n++)for(let r=1;r<=5;r++)for(let c of [3,6])for(let S of [[],[[3,4]],[[8,5],[3,7]]]){
 check(A(1,6,rep(1,n-1),[[5*n+r,c],...S]),A(0,5*n+6,rep(1,n),[[r,c],...S]),G(n),0,"general gap");gaps++;
}
for(let n=1;n<=12;n++){
 check(A(0,5*n+8,rep(1,n),[]),A(0,5*(n+1)+8,rep(1,n+1),[]),C(n),0,"root");
 roots.push({n,cost:C(n)});
}
const absolute=n=>160*2**n-7*n*n-59*n-232324;
if(absolute(11)!==93860)throw Error("entry time");
for(let n=11;n<20;n++)if(absolute(n+1)-absolute(n)!==C(n))throw Error("summed costs");
console.log(JSON.stringify({drains,gaps,roots,entryTime:absolute(11),nextTime:absolute(12)},null,2));
