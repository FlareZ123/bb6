"use strict";
// Index 8 of the frozen q0-149 frontier. Two independent repeat counts.
function build(){
const table="1RB1LC_1RC0LC_0LA0RD_1RF1RE_0RB---_1LB1RE",t=table.replaceAll("_","").match(/.{3}/g),P="010101010100000101010",B="010101010",M="1010101001000100100010100000001",D="0010001",F="00100000101000001001101010001010001001010100010101010101000001010001001";
const lit=w=>typeof w==="string",pre=w=>lit(w)?w:w[0],push=(w,s)=>lit(w)?s+w:[s+pre(w),...w.slice(1)],cut=(w,n)=>lit(w)?w.slice(n):[pre(w).slice(n),...w.slice(1)],per=(p,b,t,s)=>[p,b,t,s],eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
function step([q,l,r],known=false){
 let a=pre(l)[0];if(a===undefined){if(lit(l)&&!known)a="0";else throw Error("unknown left");}
 let s=t[2*q+Number(a)];if(s==="---")throw Error("hole");
 let nq=s.charCodeAt(2)-65;
 if(s[1]==="L")return[nq,cut(l,1),push(r,s[0])];
 let b=pre(r)[0];if(b===undefined){if(lit(r)&&!known)b="0";else throw Error("unknown right");}
 return[nq,push(cut(l,1),b+s[0]),cut(r,1)];
}
const e=(w,n,m)=>lit(w)?w:w[0]+w[1].repeat(w[2]?m:n)+e(w[3],n,m);
function find(z){let [q,l,r]=z;for(let dir of ["L","R"]){let W=dir==="L"?l:r,Oth=dir==="L"?r:l;if(lit(W))continue;let [p,I,tag,post]=W;if(p.length>32)continue;for(let j=0;j<=Math.min(30,pre(Oth).length);j++){let pO=pre(Oth).slice(0,j),lp=dir==="L"?p:pO,rp=dir==="L"?pO:p;let u=dir==="L"?[q,lp+I,rp]:[q,lp,rp+I];for(let k=1;k<=100;k++){try{u=step(u,true)}catch{break}if(u[0]!==q)continue;let C=dir==="L"?u[1]:u[2],E=dir==="L"?u[2]:u[1];if(C!==p||!E.startsWith(pO)||E.length!==pO.length+I.length)continue;let O=E.slice(pO.length),L=dir==="L"?post:cut(Oth,lp.length),R=dir==="L"?cut(Oth,rp.length):post;return {z:dir==="L"?[q,push(L,lp),per(rp,O,tag,R)]:[q,per(lp,O,tag,L),push(R,rp)],op:[dir,lp,rp,I,O,tag,L,R,k]}}}}}
let src=[2,"0",[P.slice(1)+B.repeat(7),B,false,[M,D,true,F]]],z=src,ops=[],cost=[0,0,0],done=false;
// Discover the exact symbolic return; no sampling is used as evidence of generality.
const target=[2,"0",[P.slice(1)+B.repeat(7)+"01",B.slice(2)+B.slice(0,2),false,[B.slice(2)+M+D,D,true,F]]];
for(let i=0;i<10000;i++){
 if(eq(z,target)){done=true;break}
 let a=find(z);if(a){z=a.z;ops.push(a.op);cost[a.op[5]?1:0]+=a.op[8];continue}
 z=step(z);cost[2]++;if(typeof ops.at(-1)==="number")ops[ops.length-1]++;else ops.push(1);
}
if(!done||!eq(cost,[480,0,6112]))throw Error("exact symbolic target or cost mismatch");
const family=(n,m)=>P+B.repeat(7+n)+M+D.repeat(m)+F;
let seed=[0,"",""];for(let i=0;i<34254;i++)seed=step(seed);
if(seed[0]!==2||seed[1].replace(/0+$/,"")!==""||("0"+seed[2]).replace(/0+$/,"")!==family(0,0))throw Error("blank seed mismatch");
// A^n XY = XY (YX)^n for A=XY, by induction. Thus the structurally
// checked target is exactly source(n+1,m+1), using associativity and XY=B.
if(B!=="01"+B.slice(2))throw Error("rotation");
return {table,seed,seedSteps:34254,P,B,M,D,F,src,target,ops,cost};
}
if(require.main===module)console.log(JSON.stringify(build(),null,2));
module.exports={build};
