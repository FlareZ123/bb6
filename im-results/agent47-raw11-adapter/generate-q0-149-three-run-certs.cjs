"use strict";
function build(){
const tables=["1RB1LC_1RC0LF_0LA0RD_1RA1RE_1LF1RD_---0LB","1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1LC0LF","1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1RC0LF"];
const lit=w=>typeof w==="string",pre=w=>lit(w)?w:w[0],push=(w,s)=>lit(w)?s+w:[s+pre(w),...w.slice(1)],cut=(w,n)=>lit(w)?w.slice(n):[pre(w).slice(n),...w.slice(1)];
const assert=(a,msg)=>{if(!a)throw Error(msg)},eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const per=(p,b,t,s)=>[p,b,t,s],tail=(p,t)=>[p,t];
function evalw(w,n,m,X,Y){if(lit(w))return w;if(w.length===2)return w[0]+(w[1]?Y:X);return w[0]+w[1].repeat(w[2]?m:n)+evalw(w[3],n,m,X,Y)}
function step(t,[q,l,r],known=false){
 let a=pre(l)[0];if(a===undefined){if(lit(l)&&!known)a="0";else throw Error("unknown left "+JSON.stringify([q,l,r]));}
 let s=t[2*q+Number(a)];assert(s!=="---","hole");
 let nq=s.charCodeAt(2)-65;
 if(s[1]==="L")return[nq,cut(l,1),push(r,s[0])];
 let b=pre(r)[0];if(b===undefined){if(lit(r)&&!known)b="0";else throw Error("unknown right "+JSON.stringify([q,l,r]));}
 return[nq,push(cut(l,1),b+s[0]),cut(r,1)];
}
function certify(t,src,plan){
 let z=src,ops=[],a=0,b=0,c=0;
 const trace=[];
 function run(k){if(!k)return;for(let i=0;i<k;i++)z=step(t,z);ops.push(k);c+=k;}
 function sweep(dir,lp,rp,I,O,k){
  const [q,l,r]=z;let W=dir==="L"?l:r,Other=dir==="L"?r:l;
  const preW=dir==="L"?lp:rp,preO=dir==="L"?rp:lp;
  assert(Array.isArray(W)&&W.length===4&&W[0]===preW&&W[1]===I,"sweep word "+JSON.stringify({z,dir,lp,rp,I,O}));
  assert(pre(Other).startsWith(preO),"sweep opposite");
  let tag=W[2],L=dir==="L"?W[3]:cut(Other,lp.length),R=dir==="L"?cut(Other,rp.length):W[3];
  let local=dir==="L"?[q,lp+I,rp]:[q,lp,rp+I];for(let i=0;i<k;i++)local=step(t,local,true);
  assert(eq(local,dir==="L"?[q,lp,rp+O]:[q,lp+O,rp]),"sweep identity");
  z=dir==="L"?[q,push(L,lp),per(rp,O,tag,R)]:[q,per(lp,O,tag,L),push(R,rp)];
  ops.push([dir,lp,rp,I,O,tag,L,R,k]);if(tag)b+=k;else a+=k;
 }
 plan(run,sweep,()=>z);
 return {src,target:z,ops,cost:[a,b,c]};
}
return tables.map((table,j)=>{
 const t=table.replaceAll("_","").match(/.{3}/g),sw=[7,5,7][j],f2=[5,3,5][j],f1=[4,2,4][j];
 const certs={};
 const C=(name,src,plan)=>certs[name]=certify(t,src,plan);
 const evenSrc=w=>[2,tail("00",false),per("1011","11",false,w)];
 const even=(run,sweep)=>{run(7);sweep("R","1","1","11","11",2);run(2)};
 C("init",[0,per("1","1",false,tail("00",false)),"0"],(run,sweep)=>{run(1);sweep("L","","10","1","1",sw)});
 C("odd",[2,per("00","1",true,""),per("101","11",false,tail("0",true))],(run,sweep)=>{run(7);sweep("R","1","","11","11",2);run(2);sweep("L","1","","11","00",2);run(f2+1+sw);sweep("L","","10","1","1",sw)});
 C("reduce",evenSrc(tail("0000",true)),(run,sweep)=>{even(run,sweep);run(4+1+4*sw);sweep("L","","10","11","11",2*sw)});
 C("end",evenSrc("01"),(run,sweep)=>{even(run,sweep);run(1)});
 for(let d of [1,3])C("turn"+d,evenSrc("000"+"1".repeat(d)),(run,sweep)=>{even(run,sweep);run(3+d+4+1+(d+1)*sw+1+1+4*sw);sweep("L","","10","11","11",2*sw)});
 C("five",evenSrc("011111"),(run,sweep)=>{even(run,sweep);run(9+4+f1+2*sw);sweep("L","","10","11","11",2*sw)});
 for(const [name,ce] of Object.entries(certs)){
   for(let n=0;n<4;n++)for(let m=0;m<4;m++){let X="1101",Y="101",src=[ce.src[0],evalw(ce.src[1],n,m,X,Y),evalw(ce.src[2],n,m,X,Y)],dst=[ce.target[0],evalw(ce.target[1],n,m,X,Y),evalw(ce.target[2],n,m,X,Y)];let z=src;for(let i=0;i<ce.cost[0]*n+ce.cost[1]*m+ce.cost[2];i++)z=step(t,z);assert(eq(z,dst),"sample composition mismatch");}
 }
 return {index:[11,16,17][j],table,certs};
});
}
if(require.main===module)console.log(JSON.stringify(build(),null,2));
module.exports={build};
