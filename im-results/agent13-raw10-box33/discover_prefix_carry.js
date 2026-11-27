// Finite greatest-fixed-point search for exact two-stack prefix macro certificates.
// Discovery is untrusted; generated Lean proofs check every arbitrary-tail identity.
function words(n){let a=[""];for(let k=1;k<=n;k++)for(let i=0;i<1<<k;i++)a.push(i.toString(2).padStart(k,"0"));return a}
function discover(m,B,D,Lmax=2,Rmax=2,maxSteps=40) {
 const lp=words(Lmax),rp=words(Rmax),modes=[],idx=new Map();
 function key(q,a,l,r){return q+":"+a+":"+l+":"+r}
 for(let q=0;q<6;q++)for(let a=0;a<2;a++)for(let l of lp)for(let r of rp){idx.set(key(q,a,l,r),modes.length);modes.push({q,a,l,r})}
 const ds=new Set(D),bs=new Set(B),K=D[0].length,H=B[0].length;
 if(B.some(x=>x.length!==H)||D.some(x=>x.length!==K)||!D.includes("0".repeat(K)))throw Error("invalid block alphabets");
 const cases=[];for(let ld=-1;ld<B.length;ld++)for(let rd=0;rd<D.length;rd++)cases.push({ld,rd});
 function factor(w,max,k,set,alphabet){
   let out=[];for(let p=0;p<=Math.min(w.length,max);p++)if((w.length-p)%k===0){let ws=[];for(let i=p;i<w.length;i+=k)ws.push(w.slice(i,i+k));if(ws.every(d=>set.has(d)))out.push({pre:w.slice(0,p),ws:ws.map(x=>alphabet.indexOf(x))})}
   return out;
 }
 function factL(l){
   const tail=l.at(-1),w=l.slice(0,-1);
   if(tail==="L")return factor(w,Lmax,H,bs,B);
   const core=w.replace(/0+$/,""),out=[],seen=new Set();
   for(let z=0;z<=Lmax+H;z++)for(const x of factor(core+"0".repeat(z),Lmax,H,bs,B)){let k=JSON.stringify(x);if(!seen.has(k)){seen.add(k);out.push(x)}}
   return out;
 }
 function factR(r){
   if(r.length<2)return [];
   let a=Number(r[0]);if(!Number.isFinite(a))return [];
   return factor(r.slice(1,-1),Rmax,K,ds,D).map(x=>({...x,a}));
 }
 function transitions(md,cs){
   let q=md.q,l=md.l+(cs.ld<0?"Z":B[cs.ld]+"L"),r=String(md.a)+md.r+D[cs.rd]+"R",out=new Map();
   for(let t=1;t<=maxSteps;t++){
     let b=r[0];if(b==="R")break;let v=m[q*2+Number(b)]-1;if(v<0)break;
     let w=String(v>>1&1);q=v>>2;
     if(v&1){l=w+l;r=r.slice(1)}
     else {if(l[0]==="L")break;let lb=l[0]==="Z"?"0":l[0];r=lb+w+r.slice(1);if(l[0]!=="Z")l=l.slice(1)}
     for(let u of factL(l))for(let y of factR(r)){
       let j=idx.get(key(q,y.a,u.pre,y.pre));if(j===undefined)continue;
       if(!out.has(j))out.set(j,{j,t,ls:u.ws,rs:y.ws});
     }
   }
   return [...out.values()];
 }
 let rows=modes.map(md=>cases.map(cs=>transitions(md,cs)));
 let good=modes.map(()=>true),count=good.length;
 for(;;){let del=[];for(let i=0;i<good.length;i++)if(good[i]&&rows[i].some(ts=>!ts.some(x=>good[x.j])))del.push(i);if(!del.length)break;for(let i of del)good[i]=false;count-=del.length;if(!count)break}
 const start=idx.get(key(0,0,"",""));if(!good[start])return null;
 let todo=[start],seen=new Set(todo),rules=[];
 for(let k=0;k<todo.length;k++){
   let i=todo[k];let selected=rows[i].map(ts=>ts.filter(x=>good[x.j]).sort((a,b)=>Number(!seen.has(a.j))-Number(!seen.has(b.j))||(modes[a.j].l.length+modes[a.j].r.length)-(modes[b.j].l.length+modes[b.j].r.length)||a.t-b.t||a.j-b.j)[0]);
   for(let x of selected)if(!seen.has(x.j)){todo.push(x.j);seen.add(x.j)}rules.push(selected);
 }
 return {B,D,Lmax,Rmax,maxSteps,viable:count,modes:todo.map(i=>modes[i]),cases,rules:rules.map(xs=>xs.map(x=>({...x,j:todo.indexOf(x.j)})))};
}
module.exports={discover};
if(require.main===module){
  const fs=require("fs"),path=require("path");
  const machines=JSON.parse(fs.readFileSync(path.join(__dirname,"d17v22-hard.json"),"utf8")).machines;
  const ids=process.argv.slice(2).map(Number);
  const records={};
  for(const i of ids){
    const D0=["000","100","010","110"],D1=["000","100","001","101"];
    let a=discover(machines[i],["011"],D0,2,2,30),b=discover(machines[i],["011"],D1,2,2,30);
    let c=a&&b?(a.modes.length<=b.modes.length?a:b):a||b;
    if(c)records[i]={machine:machines[i],...c};
  }
  console.log(JSON.stringify(records,null,2));
}
