/*
 * Raw36 second exceptional leaf. Untrusted source-level symbolic-sweep discovery.
 * Usage: node find_pump.js [--depth N] [--nodes N] [--sweeps N]
 * The generated operators are intended for Agent46AutoPump.check, not proof by simulation.
 */
const TABLE="1RB0LB_1RC0LA_0RD1RE_0LD1LB_0RF---_1LD0RA";
const tr=TABLE.split("_").map(s=>[s.slice(0,3),s.slice(3,6)]);
const W=(pre,block="",post=null)=>({pre,block,post:block?(post||W("")):null});
const C=(q,l,r)=>({q,l,r});
const push=(w,s)=>W(s+w.pre,w.block,w.post);
const keyW=w=>!w.block?"("+w.pre+")":"("+w.pre+","+w.block+","+keyW(w.post)+")";
const keyC=z=>z.q+"|"+keyW(z.l)+"|"+keyW(z.r);
const grow=(w,d)=>w.block?W(w.pre+w.block.repeat(d),w.block,grow(w.post,d)):w;
function normW(w){if(!w.block)return w;let p=w.pre,b=w.block,s=w.post;while(p&&p.at(-1)===b.at(-1)){let c=p.at(-1);p=p.slice(0,-1);b=c+b.slice(0,-1);s=push(s,c)}return W(p,b,normW(s))}
const normC=z=>C(z.q,normW(z.l),normW(z.r));
function step(z){
 let {q,l,r}=z;
 if(!l.pre&&l.block)return null;
 const a=l.pre?l.pre[0]:"0",s=tr[q][+a];
 if(s==="---")return null;
 const nq=s.charCodeAt(2)-65,w=s[0],dir=s[1];
 const nl=l.pre?W(l.pre.slice(1),l.block,l.post):l;
 if(dir==="R"){
   if(!r.pre&&r.block)return null;
   const b=r.pre?r.pre[0]:"0",nr=r.pre?W(r.pre.slice(1),r.block,r.post):r;
   return C(nq,push(nl,b+w),nr)
 }
 return C(nq,nl,push(r,w));
}
function localStep(z) {
 const [q,l,r]=z;if(!l)return null;
 const s=tr[q][+l[0]];if(s==="---")return null;
 const w=s[0],dir=s[1],nq=s.charCodeAt(2)-65;
 if(dir==="R"){if(!r)return null;return[nq,r[0]+w+l.slice(1),r.slice(1)]}
 return[nq,l.slice(1),w+r];
}
function sweeps(z,limit=100) {
 const out=[];
 for(const d of ["R","L"]){
   const a=d==="R"?z.l:z.r,b=d==="R"?z.r:z.l;
   if(!b.block)continue;
   const rp=b.pre,I=b.block;
   for(let f=0;f<=a.pre.length;f++){
     const lp=a.pre.slice(0,f),L=W(a.pre.slice(f),a.block,a.post),R=b.post;
     let st=d==="R"?[z.q,lp,rp+I]:[z.q,rp+I,lp];
     for(let k=1;k<=limit;k++){
       st=localStep(st);if(!st)break;
       let[q,x,y]=st;if(d==="L") [x,y]=[y,x];
       if(q===z.q&&y===rp&&x.startsWith(lp)&&x.length===lp.length+I.length){
         const O=x.slice(lp.length),aa=W(lp,O,L),bb=push(R,rp);
         const next=d==="R"?C(q,aa,bb):C(q,bb,aa);
         out.push({next,op:{dir:d,lp,rp,I,O,k,L,R}});break;
       }
     }
   }
 }
 return out;
}
const bits=s=>[...s].map(x=>x==="1"?"true":"false").join(",");
function wordLean(w){return w.block?
  "(.periodic ["+bits(w.pre)+"] ["+bits(w.block)+"] "+wordLean(w.post)+")":
  "(.lit ["+bits(w.pre)+"])";}
function opLean(op){if(op==="step")return ".step";
 return "."+(op.dir==="R"?"right":"left")+
 " ["+bits(op.lp)+"] ["+bits(op.rp)+"] ["+bits(op.I)+"] ["+bits(op.O)+
 "] "+wordLean(op.L)+" "+wordLean(op.R)+" "+op.k;
}
function concrete(m,k) {
 const line="11100".repeat(m)+"1100", cells=new Map();
 [...line].forEach((v,i)=>{if(v==="1")cells.set(i,1)});
 let state=3,pos=line.length-1;
 for(let j=0;j<k;j++){const s=tr[state][cells.get(pos)||0];if(s==="---")return null;if(s[0]==="1")cells.set(pos,1);else cells.delete(pos);pos+=s[1]==="R"?1:-1;state=s.charCodeAt(2)-65}
 const goal="11100".repeat(m+6)+"1100",shift=26;
 return {m,ok:state===3&&pos===line.length+3&&cells.size===goal.split("").filter(x=>x==="1").length&&[...goal].every((v,i)=>(cells.get(i-shift)||0)===(v==="1"?1:0)),pos};
}
const f=C(3,W("0011"+"00111".repeat(3),"00111",W("")),W(""));
const goal=keyC(normC(C(3,grow(f.l,6),grow(f.r,6))));
function solve(maxDepth,maxNodes,maxSweeps){
 let nodes=0,seen=new Map(),path=[],maxDep=0,result=null,best=null;
 function dfs(z,ns,depth){
   ++nodes;maxDep=Math.max(depth,maxDep);
   if(keyC(normC(z))===goal && path.length){result=[...path];return true}
   if(depth>maxDepth||ns>maxSweeps||nodes>maxNodes)return false;
   const key=keyC(z),prev=seen.get(key);
   if(prev && prev.d<=depth&&prev.s<=ns)return false;
   seen.set(key,{d:depth,s:ns});
   if(!best||depth>best.depth)best={depth,ns,state:key.slice(0,180)};
   const sw=sweeps(z);
   for(const {next,op} of sw){if(keyC(next)===key)continue;path.push(op);
     if(dfs(next,ns+1,depth+1))return true;
     path.pop();
   }
   const y=step(z);
   if(y){path.push("step");if(dfs(y,ns,depth+1))return true;path.pop();}
   return false;
 }
 const yes=dfs(f,0,0);
 return {yes,nodes,maxDep,seen:seen.size,best,
  ops:result, lean:result&&result.map(opLean),cost:result&&{
    a:result.filter(x=>x!=="step").reduce((s,x)=>s+x.k,0),
    b:result.filter(x=>x==="step").length}, certPrefix:wordLean(f.l)};
}
const args=typeof process==="undefined"?[]:process.argv.slice(2);
const flag=(name,def)=>{const i=args.indexOf(name);return i>=0?+args[i+1]:def};
const found=solve(flag("--depth",1100),flag("--nodes",250000),flag("--sweeps",16));
const output=typeof console!=="undefined"?x=>console.log(x):x=>text(x);
output(JSON.stringify({source:TABLE,tests:[2,3,9,15].map(m=>concrete(m,84*m+602)),solved:found.yes,nodes:found.nodes,maximumDepth:found.maxDep,seen:found.seen,best:found.best,steps:found.ops?.length,cost:found.cost,ops:found.lean},null,2));
