"use strict";
function decoder(H=6,W=3,K=8,Rmax=12,limit=2000000,mode="repair",ms=12000){
 const A=2,J=3,T=6,la=x=>Math.floor((x-1)/3)+1,lg=x=>(x-1)%3;
 const sym=(a,g,o)=>((a*16+g)*2+o),ra=x=>Math.floor(x/32),rg=x=>Math.floor(x/2)%16,orig=x=>x%2,mk=(a,g)=>sym(a,g,0),x=mk(1,1),e=mk(1,0);
 function next(q){if(q===4)return [];if(q===2)return [[sym(1,1,1),0]];if(q===3)return [[sym(2,1,1),0]];return [[sym(3+q,3,1),0],[sym(3+q,3,1),2],[sym(4+q,3,1),1],[sym(4+q,3,1),3],[sym(1+q,0,1),4]]}
 function ensure(r,q){if(r.length||q===4)return [{r,q}];return next(q).map(([s,t])=>({r:[s],q:t}))}
 const seen=new Map,states=[],queue=[],edges=[],bad=[],done=[],start=Date.now();
 function intern(s,pre=null,tag=""){let key=[s.p,s.z,s.q,s.l.join(","),s.r.join(",")].join(";");if(seen.has(key))return seen.get(key);let i=states.length;seen.set(key,i);states.push({...s,pre,tag});queue.push(i);edges.push([]);return i}
 for(let q of [1,3])intern({p:"B",z:0,q,l:[J],r:[sym(1,1,1)]},null,"start"+q);
 let qi=0,ne=0,maxl=0,maxr=0,maxrun=0,flushed=0,cut=false;
 function show(s){return {p:s.p,z:s.z,q:s.q,l:s.l.map(v=>la(v)+"/"+lg(v)),r:s.r.map(v=>ra(v)+"/"+rg(v)+(orig(v)?"o":"g")),tag:s.tag}}
 while(qi<queue.length&&!bad.length){
 if(qi>=limit||Date.now()-start>ms){cut=true;break}let i=queue[qi++],s=states[i],{p,z,q,l,r}=s;
 function fail(reason,tag){bad.push({i,reason,tag})}
 function out(p,z,q,l,r,tag,progress=false){if(l.some(v=>la(v)>K)){fail("left run overflow",tag);return}if(r.some(v=>ra(v)>Rmax)){fail("right run overflow",tag);return}let gen=r.filter(v=>!orig(v)).length;if(gen>W){fail("right work buffer overflow",tag);return}
 maxl=Math.max(maxl,l.length);maxr=Math.max(maxr,gen);for(let v of r)maxrun=Math.max(maxrun,ra(v));let emit=l.length>H?l.slice(H).reverse():[];flushed+=emit.length;
 let j=intern({p,z,q,l:l.slice(0,H),r},i,tag);edges[i].push({j,progress,emit});ne++;
 }
 function B(q,l,r,t,pr=false){out("B",0,q,l,r,t,pr)}
 function D(z,q,l,r,t,pr=false){out("D",z,q,l,r,t,pr)}
 function incR(r){return r.length?[sym(ra(r[0])+1,rg(r[0]),orig(r[0])),...r.slice(1)]:[e]}
 function incL(l){if(!l.length)return null;return [l[0]+3,...l.slice(1)]}
 function sub(r,n){let a=ra(r[0]),g=rg(r[0]);if(a===n)return{r:r.slice(1),z:g,pr:!!orig(r[0])};return{r:[sym(a-n,g,orig(r[0])),...r.slice(1)],z:0,pr:false}}
 if(!r.length&&q!==4){for(let v of ensure(r,q))out(p,z,v.q,l,v.r,"load",false);continue}
 if(p==="B"&&r.length===1&&ra(r[0])===1&&rg(r[0])===0&&q===4){done.push(i);continue}
 if(p==="B"){
 if(!r.length){fail("blank W","B");continue}
 if(!l.length){fail("protected suffix read","B");continue}
 let a=la(l[0]),g=lg(l[0]),v=l.slice(1);
 if(mode==="repair"&&!(a<=2||a===3&&g===2)){fail("unsafe B "+a+"/"+g,"B");continue}
 if(mode==="repair"&&a===3&&g===2){B(q,[A,...v],[x,...incR(r)],"repair");continue}
 if(a%2===0){let w=[mk(1,a-1),...r];if(g===2)B(q,[A,...v],w,"even");else {let u=incL(v);if(!u)fail("protected suffix increment","even");else B(q,u,w,"even")}}
 else if(g===2)D(0,q,v,[mk(1,a+2),...r],"odd gap2");
 else {if(!v.length){fail("protected suffix read","F");continue}let b=la(v[0]),h=lg(v[0]),u=v.slice(1),w=[mk(b+1,a+2),...r];if(h===1)D(0,q,u,w,"F exit");else B(q,u,w,"F loop")}
 }else{
 if(!r.length){B(q,l,[e],"blank reversal");continue}
 if(z>=2){B(q,l,z===2?incR(r):[mk(1,z-2),...r],"00");continue}
 if(z===1){let a=sub(r,1);D(a.z,q,[A,...l],a.r,"01",a.pr);continue}
 let a=ra(r[0]),g=rg(r[0]),v=r.slice(1),pr=!!orig(r[0]);
 if(a>=3){let t=sub(r,3);D(t.z,q,[J,...l],t.r,"111",t.pr)}
 else if(a===2){let u=incL(l);if(!u)fail("protected suffix increment","110");else D(Math.max(g-1,0),q,[A,...u],v,"110",pr)}
 else if(g===0||g>=3)D(Math.max(g-3,0),q,[T,...l],v,"1000",pr);
 else if(g===2)fail("fatal D 1001","D");
 else for(let w of ensure(v,q)){if(!w.r.length){fail("missing second run","101?");continue}let b=ra(w.r[0]),h=rg(w.r[0]);if(b>=2){let t=sub(w.r,2);D(t.z,w.q,[A,A,...l],t.r,"1011",pr||t.pr)}else{let pr2=!!orig(w.r[0]);for(let u of ensure(w.r.slice(1),w.q))B(u.q,[A,...l],!u.r.length?[e]:h===1?incR(u.r):[mk(1,h-1),...u.r],"1010",pr||pr2)}}
 }
 }
 let wit=null;if(bad.length){let i=bad[0].i,w=[];while(i!==null){w.push(show(states[i]));i=states[i].pre}wit=w.reverse()}
 let cycle=null,topo=0;if(!cut&&!bad.length){let indeg=new Int32Array(states.length);for(let es of edges)for(let a of es)if(!a.progress)indeg[a.j]++;let q=[];for(let i=0;i<indeg.length;i++)if(!indeg[i])q.push(i);for(let k=0;k<q.length;k++)for(let a of edges[q[k]])if(!a.progress&&!--indeg[a.j])q.push(a.j);topo=q.length;if(topo!==states.length)cycle=states.findIndex((s,i)=>indeg[i]>0)}
 return {H,W,K,Rmax,mode,states:states.length,processed:qi,edges:ne,done:done.length,maxl,maxr,maxrun,flushed,cut,bad:bad[0],witness:wit?{len:wit.length,first:wit.slice(0,5),last:wit.slice(-20)}:null,topo,cycle,complete:!cut&&!bad.length&&qi===queue.length,ms:Date.now()-start,graph:{states,edges,done}}
}
if(require.main===module){const r=decoder(...process.argv.slice(2).map(Number));delete r.graph;console.log(JSON.stringify(r,null,2))}
module.exports=decoder;
