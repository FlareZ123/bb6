"use strict";
// Experimental exact-right run-stack PDS with finite left prefix and learned factor closure.
// No decision unless complete=true, no BAD, and mathematical abstraction soundness is checked.
function dual(h=3,K=8,R=8,m=h,limit=2000000,mode="repair",msLimit=15000,witness=true,exactRight=false){
const L=(a,g)=>1+3*(a-1)+g,la=x=>Math.floor((x-1)/3)+1,lg=x=>(x-1)%3,A=L(1,1),J=L(1,2),T=L(2,2),E=L(1,0),stride=K+3;
const cls=a=>a<=R?a:exactRight?-1:R+1+(a-R-1)%3,rr=(a,g)=>cls(a)<0?-1:stride*cls(a)+g,ra=x=>Math.floor(x/stride),rg=x=>x%stride,RE=rr(1,0);
function sub(x,n){let a=ra(x),g=rg(x),out=[];for(let t of a>R?[a,a+3]:[a]){if(t===n)out.push({pop:true,g});else if(t>n)out.push({x:rr(t-n,g)});else throw Error("sub")}return out}
const inc=x=>rr(ra(x)+1,rg(x));
const sts=[],ids=new Map,ev=[],events=new Map,pending=new Set,edges=[],eps=[],pred=[],succ=[],controls=[],bad=[],gram=new Map,deps=new Map,records=[];
let ix=0,nedge=0,neps=0,ngrams=0,curr=null,cut=false;
function st(key,control=false,obj=null){if(ids.has(key))return ids.get(key);let i=sts.length;ids.set(key,i);sts.push({key,obj});controls.push(control);edges.push(new Map);eps.push(new Map);pred.push(new Set([i]));succ.push(new Set([i]));return i}
function C(p,z,l){return st("C|"+p+";"+z+";"+l.join(","),true,{p,z,l})}
const acc=st("ACCEPT");
function sched(e){if(pending.has(e.id))return;pending.add(e.id);ev.push(e)}
function trigger(p,a,v,via,eid){if(!controls[p])return;let key=p+","+a+","+v;if(events.has(key))return;let e={p,a,v,via,eid,rank:records.length-1,id:events.size};events.set(key,e);sched(e)}
function rec(p,a,v,prov){let id=records.length;records.push({p,a,v,prov:witness?prov:null});return id}
function edge(p,a,v,prov){let m=edges[p];if(!m.has(a))m.set(a,new Map);let t=m.get(a);if(t.has(v))return;t.set(v,rec(p,a,v,prov));nedge++;let id=t.get(v);for(let x of pred[p])trigger(x,a,v,p,id)}
function epsilon(p,q,prov){if(succ[p].has(q))return;neps++;eps[p].set(q,rec(p,-2,q,prov));let P=[...pred[p]],Q=[...succ[q]];for(let x of P)for(let y of Q)if(!succ[x].has(y)){succ[x].add(y);pred[y].add(x);if(controls[x])for(let [a,vs]of edges[y])for(let [v,id]of vs)trigger(x,a,v,y,id)}}
function path(q,w,v,prov){if(!w.length){epsilon(q,v,prov);return}let p=q,key=sts[q].key;for(let j=0;j<w.length-1;j++){key+="|"+w[j];let t=st("T|"+key);edge(p,w[j],t,{kind:"prefix",q});p=t}edge(p,w.at(-1),v,prov)}
function addGram(v){let k=v.slice(0,-1).join(","),x=v.at(-1);if(!gram.has(k))gram.set(k,new Set);let g=gram.get(k);if(g.has(x))return;g.add(x);ngrams++;for(let e of deps.get(k)||[])sched(e)}
function factors(l){for(let i=0;i+m<=l.length;i++)addGram(l.slice(i,i+m))}
function pop(l){if(!l.length||lg(l[0])===0)return [[]];let v=l.slice(1);if(l.length===h&&lg(l.at(-1))!==0){let k=m===1?"":l.slice(-(m-1)).join(",");if(!deps.has(k))deps.set(k,new Set);deps.get(k).add(curr);return [...(gram.get(k)||[])].map(x=>[...v,x])}return [v]}
function incL(l){if(!l.length||la(l[0])===K)return null;return [L(la(l[0])+1,lg(l[0])),...l.slice(1)]}
function gen(c,x){let {p,z,l}=c,out=[];function put(p,z,l,w,tag){if(!l||!l.length){out.push({bad:"left overflow/empty",tag});return}if(w.includes(-1)){out.push({bad:"right overflow",tag});return}factors(l);out.push({q:C(p,z,l.slice(0,h)),w,tag})}function B(l,w,t){put("B",0,l,w,t)}function D(z,l,w,t){put("D",z,l,w,t)}function err(s,t){out.push({bad:s,tag:t})}
if(p==="B"){
 if(!x){err("blank W");return out}
 let a=la(l[0]),g=lg(l[0]);
 if(mode==="repair"&&!(a<=2||a===3&&g===2)){err("unsafe B "+a+"/"+g);return out}
 if(mode==="repair"&&a===3&&g===2){for(let v of pop(l))B([A,...v],[rr(1,1),inc(x)],"repair");return out}
 if(a%2===0){let w=[rr(1,a-1),x];if(g===0)B([E],w,"even terminal");else for(let v of pop(l))B(g===2?[A,...v]:incL(v),w,"even")}
 else if(g===0)B([A,E],[rr(1,a),x],"odd terminal");
 else if(g===2){for(let v of pop(l))D(0,v,[rr(1,a+2),x],"odd gap2")}
 else for(let v of pop(l)){
   if(!v.length){err("missing F");continue}let b=la(v[0]),f=lg(v[0]);
   if(f===0)D(0,[A,E],[rr(b,a+2),x],"F end");
   else for(let u of pop(v)){if(f===2)B(u,[rr(b+1,a+2),x],"F loop");else D(0,u,[rr(b+1,a+2),x],"F exit")}
 }
}else if(p==="V"){
 if(!x)B(l,[RE,0],"blank reversal");else B(l,z===0?[inc(x)]:[rr(1,z),x],"1010 reversal")
}else if(p==="J"){
 if(!x)err("missing second right run");
 else if(ra(x)===1){if(rg(x)===0)B([A,...l],[RE],"1010 terminal");else put("V",rg(x)-1,[A,...l],[],"1010")}
 else for(let s of sub(x,2))D(s.pop?s.g:0,[A,A,...l],s.pop?[]:[s.x],"1011")
}else if(p==="D"){
 if(!x)B(l,[RE,0],"blank reversal");
 else if(z>=2)B(l,z===2?[inc(x)]:[rr(1,z-2),x],"00");
 else if(z===1){for(let s of sub(x,1))D(s.pop?s.g:0,[A,...l],s.pop?[]:[s.x],"01")}
 else {let a=ra(x),g=rg(x);if(a>=3){for(let s of sub(x,3))D(s.pop?s.g:0,[J,...l],s.pop?[]:[s.x],"111")}
 else if(a===2){let v=incL(l);D(Math.max(g-1,0),v?[A,...v]:null,[],"110")}
 else if(g===0||g>=3)D(Math.max(g-3,0),[T,...l],[],"1000");
 else if(g===2)err("fatal D 1001");
 else put("J",0,l,[],"101?");
 }
}
return out}
let l0=[L(2,0)];factors(l0);let init=C("B",0,l0);path(init,[RE,0],acc,{kind:"init",q:init});
let start=Date.now();while(ix<ev.length){if(ix>=limit||Date.now()-start>msLimit){cut=true;break}let e=ev[ix];ev[ix++]=null;pending.delete(e.id);curr=e;for(let x of gen(sts[e.p].obj,e.a)){if(x.bad){bad.push({event:e,reason:x.bad,tag:x.tag});continue}path(x.q,x.w,e.v,{kind:"rule",event:e,q:x.q,w:x.w,tag:x.tag})}if(bad.length){break}}
const co=new Set([acc]),back=Array.from({length:sts.length},()=>new Set);for(let p=0;p<sts.length;p++){for(let q of eps[p].keys())back[q].add(p);for(let vs of edges[p].values())for(let q of vs.keys())back[q].add(p)}let todo=[acc];for(let i=0;i<todo.length;i++)for(let p of back[todo[i]])if(!co.has(p)){co.add(p);todo.push(p)}
function showC(c){return {...c,l:c.l.map(v=>la(v)+"/"+lg(v))}}
function showR(x){return x?((ra(x)>R?"big"+(ra(x)%3):ra(x))+"/"+rg(x)):"$"}
function findPath(p,q,onlyEps=false,max=Infinity){if(p===q)return [];let seen=new Map([[p,-1]]),queue=[p];for(let i=0;i<queue.length&&!seen.has(q);i++){let u=queue[i],out=[...eps[u]];if(!onlyEps)for(let vs of edges[u].values())out.push(...vs);for(let [v,id]of out)if(id<=max&&!seen.has(v)){seen.set(v,id);queue.push(v)}}if(!seen.has(q))throw Error("path missing "+p+" "+q);let a=[];for(let v=q;v!==p;){let id=seen.get(v);a.push(id);v=records[id].p}return a.reverse()}
function origin(e){return [...findPath(e.p,e.via,true,e.rank),e.eid]}
function conf(pth){let c=records[pth[0]].p;return {c,stack:pth.map(i=>records[i].a).filter(x=>x>=0)}}
function extract(e){let pth=[...origin(e),...findPath(e.v,acc)],rev=[],count=0;for(;count<100000;count++){let z=conf(pth);if(z.c===init&&z.stack.length===2&&z.stack[0]===RE&&z.stack[1]===0)return{count,trace:rev.reverse(),ok:true};let v=null,len=0;for(let j=0;j<Math.min(4,pth.length);j++){let f=records[pth[j]].prov;if(f?.kind==="rule"&&f.q===z.c&&((f.w.length===0&&j===0)||f.w.length===j+1)){v=f;len=j+1;break}if(records[pth[j]].a===-2)break}if(!v)return{count,ok:false,error:"no rule prefix",config:z,first:pth.slice(0,5).map(i=>records[i])};let prior=[...origin(v.event),...pth.slice(len)];let b=conf(prior);rev.push({from:showC(sts[b.c].obj),r:b.stack.map(showR),tag:v.tag,to:showC(sts[z.c].obj),rout:z.stack.map(showR)});pth=prior}return{count,ok:false,error:"trace cap"}}
let goodBad=bad.filter(x=>co.has(x.event.v));let wit=null;if(witness&&goodBad.length){try{let e=extract(goodBad[0].event);wit={count:e.count,ok:e.ok,error:e.error,first:e.trace?.slice(0,12),last:e.trace?.slice(-12),detail:e.ok?undefined:e}}catch(e){wit={error:String(e)}}}
return{h,K,R,m,mode,exactRight,grams:ngrams,states:sts.length,controls:controls.filter(Boolean).length,edges:nedge,eps:neps,events:ix,pending:ev.length-ix,bad:goodBad.map(x=>({p:showC(sts[x.event.p].obj),a:showR(x.event.a),reason:x.reason,tag:x.tag})),cut,complete:ix===ev.length&&!bad.length,ms:Date.now()-start,witness:wit}
}
if(require.main===module){let [h,K,R,m,limit,mode,ms,witness,exact]=process.argv.slice(2);console.log(JSON.stringify(dual(+(h||3),+(K||8),+(R||8),+(m||h||3),+(limit||2000000),mode||"repair",+(ms||15000),witness!=="false",exact==="true"),null,2))}
module.exports=dual;
