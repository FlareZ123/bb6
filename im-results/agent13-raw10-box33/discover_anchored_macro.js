// Two-ended exact-empty variant. Neither block alphabet needs a zero digit.
function words(n){let a=[""];for(let k=1;k<=n;k++)for(let i=0;i<1<<k;i++)a.push(i.toString(2).padStart(k,"0"));return a}
function discoverExact(m,B,D,Lmax,Rmax,maxSteps,Lbase='',Rbase=''){
 const lp=words(Lmax),rp=words(Rmax),modes=[],idx=new Map(),key=(q,a,l,r)=>q+":"+a+":"+l+":"+r;
 for(let q=0;q<6;q++)for(let a=0;a<2;a++)for(let l of lp)for(let r of rp){idx.set(key(q,a,l,r),modes.length);modes.push({q,a,l,r})}
 const cases=[];for(let ld=-1;ld<B.length;ld++)for(let rd=-1;rd<D.length;rd++)cases.push({ld,rd});
 const lm=new Map(),rm=new Map();
 function factor(w,max,A){let out=[];for(let p=0;p<=Math.min(w.length,max);p++){function rec(k,ws){if(k===w.length){out.push({pre:w.slice(0,p),ws});return}for(let i=0;i<A.length;i++)if(w.startsWith(A[i],k))rec(k+A[i].length,[...ws,i]);}rec(p,[])}return out}
 function fact(s,max,A,mem,base){if(mem.has(s))return mem.get(s);const tail=s.at(-1),w=s.slice(0,-1);let out=[];if(tail!=="Z")out=factor(w,max,A);else{let core=w.replace(/0+$/,""),b=base.replace(/0+$/,"");if(b){if(core.endsWith(b))out=factor(core.slice(0,-b.length),max,A)}else for(let z=0;z<=max+Math.max(...A.map(x=>x.length));z++)out.push(...factor(core+"0".repeat(z),max,A))}mem.set(s,out);return out}
 function factR(r){if(r==="R")return [];const a=r[0]==="Z"?0:Number(r[0]),tail=r==="Z"?"Z":r.slice(1);return fact(tail,Rmax,D,rm,Rbase).map(x=>({...x,a}))}
 function transitions(md,cs){let q=md.q,l=md.l+(cs.ld<0?Lbase+"Z":B[cs.ld]+"L"),r=String(md.a)+md.r+(cs.rd<0?Rbase+"Z":D[cs.rd]+"R"),out=new Map();for(let t=1;t<=maxSteps;t++){let b=r[0];if(b==="R")break;let v=m[q*2+(b==="Z"?0:Number(b))]-1;if(v<0)break;let w=String(v>>1&1);q=v>>2;if(v&1){l=w+l;if(b!=="Z")r=r.slice(1)}else{if(l[0]==="L")break;let lb=l[0]==="Z"?"0":l[0];r=lb+w+(b==="Z"?r:r.slice(1));if(l[0]!=="Z")l=l.slice(1)}for(let u of fact(l,Lmax,B,lm,Lbase))for(let y of factR(r)){let j=idx.get(key(q,y.a,u.pre,y.pre));if(j!==undefined&&!out.has(j))out.set(j,{j,t,ls:u.ws,rs:y.ws});}}return [...out.values()]}
 let rows=modes.map(md=>{let rs=[];for(const cs of cases){let r=transitions(md,cs);if(!r.length)return null;rs.push(r)}return rs});let good=rows.map(x=>!!x),count=good.filter(Boolean).length;
 while(true){let del=[];for(let i=0;i<good.length;i++)if(good[i]&&rows[i].some(ts=>!ts.some(x=>good[x.j])))del.push(i);if(!del.length)break;for(let i of del)good[i]=false;count-=del.length}
 let q=0,l="Z",r="Z",initial=null;
 for(let t=0;t<=100&&!initial;t++){
  for(let u of fact(l,Lmax,B,lm,Lbase))for(let y of factR(r)){
   let j=idx.get(key(q,y.a,u.pre,y.pre));if(j!==undefined&&good[j]&&(!initial||u.ws.length+y.ws.length<initial.ls.length+initial.rs.length))initial={j,t,ls:u.ws,rs:y.ws}
  }
  if(initial)break;let bit=r[0]==="Z"?0:Number(r[0]),v=m[q*2+bit]-1;if(v<0)break;let w=String(v>>1&1);q=v>>2;
  if(v&1){l=w+l;if(r[0]!=="Z")r=r.slice(1)}else{let lb=l[0]==="Z"?"0":l[0];r=lb+w+(r[0]==="Z"?r:r.slice(1));if(l[0]!=="Z")l=l.slice(1)}
 }
 if(!initial)return null;const start=initial.j;
 let todo=[start],seen=new Set(todo),rules=[];for(let k=0;k<todo.length;k++){let i=todo[k];let selected=rows[i].map(ts=>ts.filter(x=>good[x.j]).sort((a,b)=>Number(!seen.has(a.j))-Number(!seen.has(b.j))||(modes[a.j].l.length+modes[a.j].r.length)-(modes[b.j].l.length+modes[b.j].r.length)||a.t-b.t||a.j-b.j)[0]);for(let x of selected)if(!seen.has(x.j)){todo.push(x.j);seen.add(x.j)}rules.push(selected)}return {B,D,Lbase,Rbase,initial,Lmax,Rmax,maxSteps,viable:count,modes:todo.map(i=>modes[i]),cases,rules:rules.map(xs=>xs.map(x=>({...x,j:todo.indexOf(x.j)})))}
}
module.exports={discoverExact};
