// Independent finite premises checker for the late crossing-splice bank.
// Node: node check_late_splice_bank.js
// The unbounded inference is the mathematical splicing lemma, not a cutoff test.
function checkBank(bank){
 function requireTrue(x,msg){if(!x)throw Error(msg)}
 function run(tr,t,h,q,n,o){
  const edge=new Map(),dep=new Map();
  for(let i=0;i<n;i++){
   const m=tr[2*q+Number(t.has(h))];requireTrue(m&&m!=="---","unassigned query "+i);
   const d=m[1]==="R"?1:-1,x=o*h;
   if(m[0]==="1")t.add(h);else t.delete(h);q=m.charCodeAt(2)-65;
   const k=Math.min(x,x+o*d);edge.set(k,(edge.get(k)||"")+(o*d>0?"R":"L")+q);
   dep.set(x,(dep.get(x)||0)+1);h+=d;
  }return {t,h,q,edge,dep}
 }
 function word(t,h,o){
  let end=0;for(const x of t){requireTrue(o*(x-h)>0,"nonblank head or exterior");end=Math.max(end,o*(x-h))}
  return Array.from({length:end},(_,i)=>t.has(h+o*(i+1))?"1":"0").join("")
 }
 function normal(w,cuts,shift,extra){
  let p=0,fixed="",out=[];
  for(let [a,b] of cuts){a-=shift;b-=shift;requireTrue(p<=a&&a<b&&b<=w.length,"invalid cut");
   let block=w.slice(a,b),tail="";
   fixed+=w.slice(p,a)+block.repeat(1+extra);
   while(fixed&&fixed.at(-1)===block.at(-1)){
    let x=fixed.at(-1);fixed=fixed.slice(0,-1);tail=x+tail;block=x+block.slice(0,-1)
   }out.push(fixed,block);fixed=tail;p=b
  }out.push(fixed+w.slice(p));return JSON.stringify(out)
 }
 const results={};
 for(const [id,c] of Object.entries(bank)){
  const tr=c.table.replaceAll("_","").match(/.../g),o=c.side==="L"?1:-1,s=c.state||0;
  requireTrue(tr.length===12&&c.period>0&&o*c.shift<=0,id+" format");
  const a=run(tr,new Set(),0,0,c.entry,o);
  requireTrue(a.h===c.entryHead&&a.q===s,id+" entry");
  const w=word(a.t,a.h,o),t=new Set([...a.t].map(x=>x-a.h)),b=run(tr,t,0,s,c.period,o);
  requireTrue(b.h===c.shift&&b.q===s,id+" exit");const f=word(b.t,b.h,o);
  let last=0,inc=0;
  for(const [u,v] of c.cuts){
   requireTrue(last<=u&&u>0&&u<v,id+" cuts");last=v;
   requireTrue((b.edge.get(u)||"")===(b.edge.get(v)||""),id+" crossing");
   for(let x=u+1;x<=v;x++)inc+=b.dep.get(x)||0;
  }
  requireTrue(inc===c.increment,id+" increment");
  requireTrue(normal(w,c.cuts,0,1)===normal(f,c.cuts,o*c.shift,0),id+" word identity");
  results[id]={entry:c.entry,period:c.period,shift:c.shift,pumps:c.cuts.length,increment:inc};
 }return results
}
if(typeof require!=="undefined"&&require.main===module)console.log(checkBank(require("./a0la-late-splice-bank.json")));
