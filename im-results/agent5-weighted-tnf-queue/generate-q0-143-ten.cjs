"use strict";
const {discover}=require("./discover-tail.cjs");
const xs=require("./q0-143-exact-frontier.json").remaining;
const old=require("./q0-143-tail-fixtures.json")[0].rules;
const common=["pop10","pop1","P11gen","P11base","initial","initialBase"];
const types=["I","I","II","II","I","I","III","I","III","I"];
const seeds=[394,394,70,70,394,394,148,352,132,468];
const plan={I:[["right0",[0,["11",0],["0","11111",0,"11111"]],[0,["11110","11110",0,["1",0]],"001"]],["right3",[0,["11",0],["0","11111",0,"111"]],[0,["1110","11110",0,["1",0]],"001"]]],II:[["right2",[0,["11",0],["0","11111",0,"11"]],[0,["1110","10110",0,["1",0]],"001"]],["right3",[0,["11",0],["0","11111",0,"111"]],[0,["1110","10110",0,["1",0]],"001"]]],III:[["right0",[0,["11",0],["0","111",0,"111"]],[0,["110","110",0,["1",0]],"001"]],["right1",[0,["11",0],["0","111",0,"1111"]],[0,["0101","101",0,["",0]],"001"]],["turn",[0,["0101",0],"001"],[0,["101101",0],"001"]]]};
function make(){
 return xs.map((table,i)=>{
  const type=types[i],rules={};
  const req=[...common.map(k=>[k,old[k].source,old[k].target]),...plan[type]];
  for(let [k,s,t] of req){
   if(i===3&&k.startsWith("right")) s=[0,["11",0],["01","11111",0,s[2][3].slice(1)]];
   const c=discover(table,s,t);if(!c.ok||c.frames)throw Error("missing "+i+" "+k);rules[k]=c;
  }
  const [k,m]=type==="I"?[3,10]:type==="II"?[2,3]:[2,6];
  return {index:i,table,type,seed:seeds[i],initial:[0,"","01".repeat(k)+"00"+"1".repeat(m)],rules};
 });
}
function verify(x){
 const ts=x.table.replaceAll("_","").match(/.{3}/g),eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
 const pre=w=>typeof w==="string"?w:w[0],push=(w,p)=>typeof w==="string"?p+w:[p+w[0],...w.slice(1)];
 const drop=w=>typeof w==="string"?w.slice(1):[w[0].slice(1),...w.slice(1)];
 const norm=w=>{
  if(typeof w==="string"||w.length===2)return w;
  let [p,b,v,s]=w;while(p&&p.at(-1)===b.at(-1)){const c=p.at(-1);p=p.slice(0,-1);b=c+b.slice(0,-1);s=push(s,c)}
  return [p,b,v,norm(s)];
 };
 const zNorm=z=>[z[0],norm(z[1]),norm(z[2])];
 const read=(w,local)=>{if(pre(w).length)return pre(w)[0];if(!local&&typeof w==="string")return "0";throw Error("unknown tail");};
 const step=(z,local=false)=>{
  const [q,l,r]=z,a=read(l,local),s=ts[2*q+Number(a)];if(s==="---")throw Error("hole");
  const nq=s.charCodeAt(2)-65;
  return s[1]==="L"?[nq,drop(l),push(r,s[0])]:[nq,push(drop(l),read(r,local)+s[0]),drop(r)];
 };
 const run=(z,k,local=false)=>{for(let j=0;j<k;j++)z=step(z,local);return z};
 const seed=run([0,"",""],x.seed);if(!eq(seed,x.initial))throw Error("seed mismatch "+x.index+" "+JSON.stringify(seed));
 for(const [name,c] of Object.entries(x.rules)){
  let z=c.source,a=0,b=0,d=0;
  for(const op of c.ops){
   if(typeof op==="number"){z=run(z,op);d+=op;continue;}
   const [dir,lp,rp,I,O,v,L,R,k]=op,q=z[0];
   if(dir==="R"){
    if(!eq(z,[q,push(L,lp),[rp,I,v,R]])||!eq(run([q,lp,rp+I],k,true),[q,lp+O,rp]))throw Error("bad right sweep");
    z=[q,[lp,O,v,L],push(R,rp)];
   }else if(dir==="L"){
    if(!eq(z,[q,[lp,I,v,L],push(R,rp)])||!eq(run([q,lp+I,rp],k,true),[q,lp,rp+O]))throw Error("bad left sweep");
    z=[q,push(L,lp),[rp,O,v,R]];
   }else throw Error("bad op");
   if(v)b+=k;else a+=k;
  }
  if(!eq(zNorm(z),zNorm(c.target))||d!==c.primitive)throw Error("bad target "+name);
  if(name.startsWith("initial")&&d===0)throw Error("zero initial");
  c.cost=[a,b,d];
 }
 return x;
}
module.exports={make,verify};
if(require.main===module)console.log(JSON.stringify(make().map(verify),null,2));
