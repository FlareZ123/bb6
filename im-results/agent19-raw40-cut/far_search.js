/* Portable 31-bit FAR saturation for up to five DFA states.
   This searches exactly the same forward/backward DFA+NFA condition as farbank.cpp.
   Successful codes are data, not trusted proof.
*/
function farCheck(table,D,rev){
 const n=D.length/2,N=6*n+1,H=N-1,halt=1<<H,T=new Int32Array(2*N),rules=[];
 let p=table.replaceAll("_","").match(/.../g).map(m=>m==="---"?-1:12*+m[0]+6*(m[1]==="R")+m.charCodeAt(2)-65);
 T[H]=T[N+H]=halt;
 let pred=Array.from({length:n},()=>[]);
 for(let j=0;j<n;j++)for(let b=0;b<2;b++)pred[D[2*j+b]].push([j,b]);
 for(let l=0;l<n;l++)for(let q=0;q<6;q++)for(let a=0;a<2;a++){
  let m=p[2*q+a],dst=a*N+6*l+q;
  if(m<0){T[dst]=halt;continue}
  let w=m>=12?1:0,r=m%12>=6?1:0,nxt=m%6;
  if(r!==rev)T[dst]=1<<(6*D[2*l+w]+nxt);
  else for(let [j,b] of pred[l])rules.push(dst,b*N+6*j+nxt,w*N);
 }
 while(true){
  let z=halt;
  while(true){let old=z;for(let j=0;j<N;j++)if(T[j]&z)z|=1<<j;if(z&1)return false;if(old===z)break}
  let changed=false;
  for(let i=0;i<rules.length;i+=3){let dst=rules[i],src=rules[i+1],off=rules[i+2],v=T[dst],bits=T[src];
   while(bits){v|=T[off+31-Math.clz32(bits&-bits)];bits&=bits-1}
   if(v!==T[dst]){T[dst]=v;changed=true}
  }
  if(!changed)return true;
 }
}
function farSearch(tables,{max=5,bank=[],maxTests=Infinity}={}){
 let todo=tables.map(([id,table])=>({id,table})),found=[],tested=0;
 function test(D,rev){
  if(!todo.length||tested>=maxTests)return;
  tested++;
  let left=[],code=String(rev)+D.join("");
  for(let t of todo)if(farCheck(t.table,D,rev))found.push({id:t.id,table:t.table,code});else left.push(t);
  todo=left;
 }
 for(let code of bank){if(code.length<=11&&code.length%2===1)test([...code.slice(1)].map(Number),+code[0]);if(!todo.length)break}
 for(let n=1;n<=max&&todo.length&&tested<maxTests;n++){
  let D=Array(2*n).fill(0);
  function dfs(i,mx){
   if(!todo.length||tested>=maxTests)return;
   if(i===2*n){if(mx===n-1){test(D,0);test(D,1)}return}
   if(Math.floor(i/2)>mx)return;
   for(let d=0;d<=Math.min(n-1,mx+1);d++){D[i]=d;dfs(i+1,Math.max(mx,d))}
  }
  dfs(1,0)
 }
 return {found,unresolved:todo,tested}
}
