// Deterministic candidate discovery; Lean checker is the trust boundary.
// Codes: 0 wildcard, 1..24 ordinary, 25 assigned halt.
const fs = require("node:fs");
function search(raw, depth=3, limit=160) {
const old=[...raw.matchAll(/^\[([0-9,]+)\],?$/gm)].map(m=>m[1].split(",").map(Number));
const start=[8,0,11,0,0,0,0,0,0,0,0,0],all=Array.from({length:25},(_,i)=>i+1);
const classify=(p)=>{let q=0,h=0,s=new Set(),prev=Array.from({length:6},()=>[]),trace=[];for(let n=0;n<=limit;n++){const a=2*q+Number(s.has(h)),v=p[a];if(v===25)return ["halt",n];if(!v)return ["hole",a,n];let lo=h,hi=h,k=n;for(let t=prev[q].length-1;t>=0;t--){let j=prev[q][t];if(n-j>128)break;while(k>j){k--;lo=Math.min(lo,trace[k][0]);hi=Math.max(hi,trace[k][0])}const [hh,ss]=trace[j],d=h-hh;for(const r of [true,false]){if(r?d<0:d>0)continue;const b=r?lo:hi,inside=x=>r?x>=b:x<=b;let ok=true;for(let x of ss)if(inside(x)&&!s.has(x+d)){ok=false;break}if(ok)for(let x of s)if(inside(x-d)&&!ss.has(x-d)){ok=false;break}if(ok)return ["cycle",j,n-j,r,b]}}prev[q].push(n);trace.push([h,new Set(s)]);const m=v-1;if(m&2)s.add(h);else s.delete(h);h+=(m&1)?1:-1;q=m>>2;}return ["long"]};
let leaves=[],open=[],skipped=[];const sub=(p,r)=>r.every((v,i)=>v===0||v===p[i]);
function visit(p,d){if(old.some(r=>sub(p,r))){skipped.push(p.slice());return}let r=classify(p),k=r[0];if(k==="hole"&&d){for(const v of all){p[r[1]]=v;visit(p,d-1);p[r[1]]=0}return}if(k==="halt"||k==="cycle")leaves.push([p.slice(),r]);else open.push([p.slice(),r]);}visit(start,depth);
const mask=(p)=>p.map(v=>v?1<<(v-1):0x1ffffff),pop=(x)=>{let k=0;while(x){x&=x-1;k++;}return k;},mass=b=>b.reduce((a,x)=>a*BigInt(pop(x)),1n);
function subtract(b,r){if(r.some((v,i)=>v&&!(b[i]&(1<<(v-1)))))return [b];let rem=b.slice(),out=[];for(let i=0;i<12;i++)if(r[i]){const bit=1<<(r[i]-1),reject=rem[i]&~bit;if(reject){const c=rem.slice();c[i]=reject;out.push(c)}rem[i]=bit}return out}
let boxes=[mask(start)];for(const r of old)boxes=boxes.flatMap(b=>subtract(b,r));
const overlap=p=>boxes.reduce((sum,b)=>sum+mass(b.map((v,i)=>v&mask(p)[i])),0n);
const sum=xs=>xs.reduce((a,x)=>a+mass(mask(x)),0n);
const before=boxes.reduce((a,b)=>a+mass(b),0n),gain=leaves.reduce((a,[p])=>a+overlap(p),0n),remain=open.reduce((a,[p])=>a+overlap(p),0n);
if(gain+remain!==before)throw Error("partition mismatch");
const stats={depth,limit,oldRows:old.length,oldBoxes:boxes.length,oldResidual:String(before),newLeaves:leaves.length,halt:leaves.filter(x=>x[1][0]==="halt").length,cycle:leaves.filter(x=>x[1][0]==="cycle").length,open:open.length,skipped:skipped.length,rawLeafMass:String(sum(leaves.map(x=>x[0]))),newlyCovered:String(gain),remaining:String(remain),maxHalt:Math.max(...leaves.filter(x=>x[1][0]==="halt").map(x=>x[1][1])),maxCycle:Math.max(...leaves.filter(x=>x[1][0]==="cycle").map(x=>x[1][1]+x[1][2]))};
return {stats,leaves,open,skipped};
}
const r=search(fs.readFileSync(process.argv[2] || "im-results/agent49-box-complement/Raw10Encoded.lean","utf8"), Number(process.argv[3] || 3));
console.log(JSON.stringify(r,null,2));
