"use strict";
function sourceMitmCert(table,L,R){
 const ds=[L,R],E=ds.map(d=>d.map(()=>new Set())),W=ds.map(d=>d.map(()=>[])),seen=new Set(),rows=[],nr=R.length,nl=L.length;
 const key=(q,a,l,r)=>((2*q+a)*nl+l)*nr+r;
 function add(q,a,l,r){let k=key(q,a,l,r);if(!seen.has(k)){seen.add(k);rows.push([q,a,l,r]);}}
 function pop(st,e){let [q,a,l,r,n,d,w]=st,b=e%2,i=e>>1;if(d)add(n,b,L[l][w],i);else add(n,b,i,R[r][w]);}
 E[0][0].add(0);E[1][0].add(0);add(0,0,0,0);
 for(let i=0;i<rows.length;i++){
  let [q,a,l,r]=rows[i],t=table.slice(6*q+3*a,6*q+3*a+3);
  if(t==="---")return null;
  let w=+t[0],d=Number(t[1]==="R"),n=t.charCodeAt(2)-65,st=[q,a,l,r,n,d,w];
  let old=d?l:r,edge=2*old+w,dest=ds[1-d][old][w],set=E[1-d][dest];
  if(!set.has(edge)){set.add(edge);for(let waiter of W[1-d][dest])pop(waiter,edge);}
  let target=d?r:l;W[d][target].push(st);for(let e of E[d][target])pop(st,e);
 }
 for(let [q,a,l,r] of rows){
  let t=table.slice(6*q+3*a,6*q+3*a+3),w=+t[0],n=t.charCodeAt(2)-65;
  if(t[1]==="R"){
   let j=L[l][w];
   if(!E[0][j].has(2*l+w)||![...E[1][r]].every(e=>seen.has(key(n,e%2,j,e>>1))))throw Error("right closure");
  }else{
   let j=R[r][w];
   if(!E[1][j].has(2*r+w)||![...E[0][l]].every(e=>seen.has(key(n,e%2,e>>1,j))))throw Error("left closure");
  }
 }
 const stack=(d,i)=>({push:d,pop:E[i].map(es=>[...es].map(e=>[e%2,e>>1]))});
 return {table,left:stack(L,0),right:stack(R,1),rows};
}
module.exports={sourceMitmCert};
